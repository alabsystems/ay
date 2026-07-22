// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use ntest::timeout;
use serde_json::Value;
use sha2::{Digest, Sha256};
use tempfile::tempdir;

use crate::spawn::OutputTimeout;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("ay crate should live under crates/ay")
        .to_path_buf()
}

fn ay() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn current_git_head() -> String {
    let output = Command::new("git")
        .current_dir(repo_root())
        .args(["rev-parse", "HEAD"])
        .output()
        .expect("spawn git rev-parse HEAD");
    assert!(
        output.status.success(),
        "git rev-parse HEAD failed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("git HEAD should be utf-8")
        .trim()
        .to_string()
}

fn current_ay_build_json() -> Value {
    serde_json::json!({
        "version": env!("CARGO_PKG_VERSION"),
        "increment": env!("AY_BUILD_INCREMENT"),
        "commit": env!("AY_BUILD_COMMIT"),
        "datetime_utc": env!("AY_BUILD_DATETIME_UTC"),
        "stamp": env!("AY_BUILD_STAMP"),
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn assert_diagnostic_only(report: &Value) {
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["model_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["proof_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["solver_verdict_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_writes_diagnostic_json() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-unsat.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 2 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\ttrue\n2\tfalse\n").expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--radius",
            "0",
            "--window",
            "gate=1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair component-window");

    assert!(
        output.status.success(),
        "sat-comp-repair should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read diagnostic JSON"))
            .expect("parse diagnostic JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-repair-probe-component-window/v1",
        "{report:#}"
    );
    assert_eq!(report["counts"]["checked_windows"], 1, "{report:#}");
    assert_eq!(report["counts"]["unsat_verified"], 1, "{report:#}");
    assert_eq!(
        report["verdict"]["all_selected_windows_unsat_verified"], true,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_applies_seed_set_file() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-seeded-window.cnf");
    let ledger = dir.path().join("w210.tsv");
    let seed = dir.path().join("seed.tsv");
    let out = dir.path().join("seeded-component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 2 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\ttrue\n2\tfalse\n").expect("write ledger");
    fs::write(&seed, "original_var\tcandidate_value\n2\ttrue\n").expect("write seed set");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--seed-set-file")
        .arg(&seed)
        .args([
            "--radius",
            "0",
            "--window",
            "gate=1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair seeded component-window");

    assert!(
        output.status.success(),
        "seeded component-window should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read seeded diagnostic JSON"))
            .expect("parse seeded diagnostic JSON");
    assert_eq!(report["assignment_overlay"]["enabled"], true, "{report:#}");
    assert_eq!(
        report["assignment_overlay"]["set_var_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["assignment_overlay"]["changed_from_w210_var_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["assignment_overlay"]["one_based_changed_from_w210_vars"],
        serde_json::json!([{ "var": 2, "value": true }]),
        "{report:#}"
    );
    assert_eq!(
        report["assignment_overlay"]["w210_residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["assignment_overlay"]["seed_residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["radius_free_vars"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["windows"][0]["window_vars_already_radius_free"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["windows"][0]["extra_outside_window_vars"], 0,
        "{report:#}"
    );
    assert_eq!(report["windows"][0]["free_total_vars"], 1, "{report:#}");
    assert_eq!(report["windows"][0]["frozen_outside_vars"], 1, "{report:#}");
    assert_eq!(report["counts"]["unsat_verified"], 1, "{report:#}");
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_low_free_windows_are_bounded() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-auto-window.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("auto-component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--radius",
            "0",
            "--auto-low-free-windows",
            "--auto-window-max-size",
            "2",
            "--window-limit",
            "4",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair auto component-window");

    assert!(
        output.status.success(),
        "auto component-window should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read auto diagnostic JSON"))
            .expect("parse auto diagnostic JSON");
    assert_eq!(
        report["probe_definition"]["window_source"], "auto_low_free",
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["auto_low_free_windows"], true,
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["auto_window_max_size"], 2,
        "{report:#}"
    );
    assert_eq!(report["probe_definition"]["window_limit"], 4, "{report:#}");
    assert_eq!(
        report["probe_definition"]["outside_radius_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["one_based_outside_radius_vars"],
        serde_json::json!([2, 3, 4]),
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["windows"],
        serde_json::json!([
            { "name": "auto-s1-v2", "one_based_vars": [2] },
            { "name": "auto-s1-v3", "one_based_vars": [3] },
            { "name": "auto-s1-v4", "one_based_vars": [4] },
            { "name": "auto-s2-v2-v3", "one_based_vars": [2, 3] }
        ]),
        "{report:#}"
    );
    for (idx, expected) in [
        ("auto-s1-v2", serde_json::json!([2])),
        ("auto-s1-v3", serde_json::json!([3])),
        ("auto-s1-v4", serde_json::json!([4])),
        ("auto-s2-v2-v3", serde_json::json!([2, 3])),
    ]
    .into_iter()
    .enumerate()
    {
        let (name, vars) = expected;
        assert_eq!(
            report["windows"][idx]["window_index"],
            idx + 1,
            "{report:#}"
        );
        assert_eq!(report["windows"][idx]["window_name"], name, "{report:#}");
        assert_eq!(
            report["windows"][idx]["one_based_window_vars"], vars,
            "{report:#}"
        );
        assert_eq!(
            report["windows"][idx]["window_vars_already_radius_free"], 0,
            "{report:#}"
        );
        assert_eq!(
            report["windows"][idx]["extra_outside_window_vars"],
            report["windows"][idx]["window_var_count"],
            "{report:#}"
        );
        assert_eq!(
            report["windows"][idx]["free_total_vars"],
            report["windows"][idx]["free_radius_vars"]
                .as_u64()
                .expect("free_radius_vars should be numeric")
                + report["windows"][idx]["window_var_count"]
                    .as_u64()
                    .expect("window_var_count should be numeric"),
            "{report:#}"
        );
    }
    assert_eq!(report["counts"]["checked_windows"], 4, "{report:#}");
    assert_eq!(report["counts"]["selected_windows"], 4, "{report:#}");
    assert_eq!(
        report["counts"]["auto_low_free_candidate_windows"], 6,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_low_free_selected_windows"], 4,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_low_free_pruned_by_window_limit"], 2,
        "{report:#}"
    );
    assert_eq!(report["counts"]["unsat_verified"], 4, "{report:#}");
    assert_eq!(
        report["verdict"]["all_selected_windows_unsat_verified"], true,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_low_free_rejects_explicit_windows() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-auto-window-mixed.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("auto-component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--radius",
            "0",
            "--window",
            "manual=2",
            "--auto-low-free-windows",
            "--auto-window-max-size",
            "2",
            "--window-limit",
            "4",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair mixed auto component-window");

    assert!(
        !output.status.success(),
        "mixed auto component-window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--auto-low-free-windows cannot be combined with explicit --window entries"),
        "stderr should explain mutually exclusive window modes:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_low_free_requires_window_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-auto-window-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("auto-component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--radius",
            "0",
            "--auto-low-free-windows",
            "--auto-window-max-size",
            "2",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair unbounded auto component-window");

    assert!(
        !output.status.success(),
        "unbounded auto component-window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--auto-low-free-windows requires --window-limit"),
        "stderr should explain bounded auto-window requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_hitting_windows_are_bounded() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-window.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-hooks.tsv");
    let out = dir.path().join("component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 8 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n5\tfalse\n6\tfalse\n7\tfalse\n8\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "1\t4\t11 12 13 14\t2\t6 7\tforced_gate_replay_bridge w210_frontier\t5\tbridge_source_frame\tbridge\n",
            "2\t5\t21 22 23 24 25\t1\t2\tforced_gate_replay_bridge w210_scc_choice\t8\tbridge_source_frame\tbridge\n",
            "3\t2\t31 32\t1\t4\tw210_frontier w210_scc_choice\t0\tmixed_frontier_scc_frame\tmixed\n",
            "6\t2\t61 62\t1\t3\tw210_frontier\t0\tpure_frontier_frame\tpure\n",
            "8\t1\t81\t1\t5\tw210_frontier\t0\tpure_frontier_frame\tpure\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-component-hitting-windows",
            "--window-limit",
            "4",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair component-hitting window");

    assert!(
        output.status.success(),
        "component-hitting component-window should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read component-hitting diagnostic JSON"),
    )
    .expect("parse component-hitting diagnostic JSON");
    assert_eq!(
        report["probe_definition"]["window_source"], "component_hitting",
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["auto_component_hitting_windows"], true,
        "{report:#}"
    );
    assert!(
        report["probe_definition"]["component_hook_targets"]["path"]
            .as_str()
            .expect("component hook artifact path")
            .ends_with("component-hooks.tsv"),
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["component_hitting_windows"],
        serde_json::json!([
            {
                "component_id": 8,
                "name": "component-8-hit-v5",
                "one_based_vars": [5],
                "min_variable_hitting_set_size": 1,
                "diagnostic_missing_literal_rows": 0,
                "clause_count": 1,
                "one_based_clause_ids": [81],
                "source_frame_class": "pure_frontier_frame",
                "covered_real_source_families": "w210_frontier",
                "construction_action": "pure"
            },
            {
                "component_id": 6,
                "name": "component-6-hit-v3",
                "one_based_vars": [3],
                "min_variable_hitting_set_size": 1,
                "diagnostic_missing_literal_rows": 0,
                "clause_count": 2,
                "one_based_clause_ids": [61, 62],
                "source_frame_class": "pure_frontier_frame",
                "covered_real_source_families": "w210_frontier",
                "construction_action": "pure"
            },
            {
                "component_id": 3,
                "name": "component-3-hit-v4",
                "one_based_vars": [4],
                "min_variable_hitting_set_size": 1,
                "diagnostic_missing_literal_rows": 0,
                "clause_count": 2,
                "one_based_clause_ids": [31, 32],
                "source_frame_class": "mixed_frontier_scc_frame",
                "covered_real_source_families": "w210_frontier w210_scc_choice",
                "construction_action": "mixed"
            },
            {
                "component_id": 2,
                "name": "component-2-hit-v2",
                "one_based_vars": [2],
                "min_variable_hitting_set_size": 1,
                "diagnostic_missing_literal_rows": 8,
                "clause_count": 5,
                "one_based_clause_ids": [21, 22, 23, 24, 25],
                "source_frame_class": "bridge_source_frame",
                "covered_real_source_families": "forced_gate_replay_bridge w210_scc_choice",
                "construction_action": "bridge"
            }
        ]),
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["windows"],
        serde_json::json!([
            { "name": "component-8-hit-v5", "one_based_vars": [5] },
            { "name": "component-6-hit-v3", "one_based_vars": [3] },
            { "name": "component-3-hit-v4", "one_based_vars": [4] },
            { "name": "component-2-hit-v2", "one_based_vars": [2] }
        ]),
        "{report:#}"
    );
    for (idx, expected) in [
        ("component-8-hit-v5", serde_json::json!([5])),
        ("component-6-hit-v3", serde_json::json!([3])),
        ("component-3-hit-v4", serde_json::json!([4])),
        ("component-2-hit-v2", serde_json::json!([2])),
    ]
    .into_iter()
    .enumerate()
    {
        let (name, vars) = expected;
        assert_eq!(
            report["windows"][idx]["window_index"],
            idx + 1,
            "{report:#}"
        );
        assert_eq!(report["windows"][idx]["window_name"], name, "{report:#}");
        assert_eq!(
            report["windows"][idx]["one_based_window_vars"], vars,
            "{report:#}"
        );
        assert_eq!(
            report["windows"][idx]["extra_outside_window_vars"],
            report["windows"][idx]["window_var_count"],
            "{report:#}"
        );
    }
    assert_eq!(
        report["counts"]["auto_component_hitting_candidate_windows"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_component_hitting_selected_windows"], 4,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_component_hitting_pruned_by_window_limit"], 1,
        "{report:#}"
    );
    assert_eq!(report["counts"]["checked_windows"], 4, "{report:#}");
    assert_eq!(report["counts"]["unsat_verified"], 4, "{report:#}");
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_hitting_requires_window_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-window-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-hooks.tsv");
    let out = dir.path().join("component-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "8\t1\t81\t1\t2\tw210_frontier\t0\tpure_frontier_frame\tpure\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-component-hitting-windows",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair unbounded component-hitting window");

    assert!(
        !output.status.success(),
        "unbounded component-hitting window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--auto-component-hitting-windows requires --window-limit"),
        "stderr should explain bounded component-window requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_hitting_rejects_other_window_modes() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-window-mixed.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-hooks.tsv");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "8\t1\t81\t1\t2\tw210_frontier\t0\tpure_frontier_frame\tpure\n",
        ),
    )
    .expect("write component hooks");

    let explicit_out = dir.path().join("component-window-explicit.json");
    let explicit_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--window",
            "manual=2",
            "--auto-component-hitting-windows",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&explicit_out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair explicit mixed component-hitting window");
    assert!(
        !explicit_output.status.success(),
        "explicit mixed component-hitting window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&explicit_output.stdout),
        String::from_utf8_lossy(&explicit_output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&explicit_output.stderr).contains(
            "--auto-component-hitting-windows cannot be combined with explicit --window entries"
        ),
        "stderr should explain explicit-window exclusion:\n{}",
        String::from_utf8_lossy(&explicit_output.stderr)
    );

    let low_free_out = dir.path().join("component-window-low-free.json");
    let low_free_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-low-free-windows",
            "--auto-component-hitting-windows",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&low_free_out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair low-free mixed component-hitting window");
    assert!(
        !low_free_output.status.success(),
        "low-free mixed component-hitting window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&low_free_output.stdout),
        String::from_utf8_lossy(&low_free_output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&low_free_output.stderr).contains(
            "--auto-low-free-windows cannot be combined with --auto-component-hitting-windows"
        ),
        "stderr should explain auto-window exclusion:\n{}",
        String::from_utf8_lossy(&low_free_output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_family_windows_are_bounded() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-family-window.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-family-hooks.tsv");
    let out = dir.path().join("component-family-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 8 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n5\tfalse\n6\tfalse\n7\tfalse\n8\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t5\t51 52 53 54 55\t2\t6 7\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t5\tbridge_source_frame\tall-three\n",
            "1\t4\t11 12 13 14\t2\t2 3\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t5\tbridge_source_frame\tall-three\n",
            "2\t5\t21 22 23 24 25\t1\t4\tforced_gate_replay_bridge w210_scc_choice\t8\tbridge_source_frame\tbridge-scc\n",
            "3\t2\t31 32\t1\t5\tw210_frontier w210_scc_choice\t0\tmixed_frontier_scc_frame\tfrontier-scc\n",
            "6\t2\t61 62\t1\t8\tw210_frontier\t0\tpure_frontier_frame\tfrontier\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-component-family-windows",
            "--window-limit",
            "3",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair component-family window");

    assert!(
        output.status.success(),
        "component-family component-window should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read component-family diagnostic JSON"),
    )
    .expect("parse component-family diagnostic JSON");
    assert_eq!(
        report["probe_definition"]["window_source"], "component_family",
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["auto_component_family_windows"], true,
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["component_family_windows"],
        serde_json::json!([
            {
                "component_ids": [5],
                "name": "component-family-c5-v6-v7",
                "one_based_vars": [6, 7],
                "covered_real_source_families": [
                    "forced_gate_replay_bridge",
                    "w210_frontier",
                    "w210_scc_choice"
                ],
                "source_frame_classes": ["bridge_source_frame"],
                "diagnostic_missing_literal_rows": 5,
                "covered_clause_count": 5,
                "one_based_clause_ids": [51, 52, 53, 54, 55],
                "component_count": 1
            },
            {
                "component_ids": [1],
                "name": "component-family-c1-v2-v3",
                "one_based_vars": [2, 3],
                "covered_real_source_families": [
                    "forced_gate_replay_bridge",
                    "w210_frontier",
                    "w210_scc_choice"
                ],
                "source_frame_classes": ["bridge_source_frame"],
                "diagnostic_missing_literal_rows": 5,
                "covered_clause_count": 4,
                "one_based_clause_ids": [11, 12, 13, 14],
                "component_count": 1
            },
            {
                "component_ids": [2, 3],
                "name": "component-family-c2-c3-v4-v5",
                "one_based_vars": [4, 5],
                "covered_real_source_families": [
                    "forced_gate_replay_bridge",
                    "w210_frontier",
                    "w210_scc_choice"
                ],
                "source_frame_classes": ["bridge_source_frame", "mixed_frontier_scc_frame"],
                "diagnostic_missing_literal_rows": 8,
                "covered_clause_count": 7,
                "one_based_clause_ids": [21, 22, 23, 24, 25, 31, 32],
                "component_count": 2
            }
        ]),
        "{report:#}"
    );
    assert_eq!(
        report["probe_definition"]["windows"],
        serde_json::json!([
            { "name": "component-family-c5-v6-v7", "one_based_vars": [6, 7] },
            { "name": "component-family-c1-v2-v3", "one_based_vars": [2, 3] },
            { "name": "component-family-c2-c3-v4-v5", "one_based_vars": [4, 5] }
        ]),
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_component_family_candidate_windows"], 27,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_component_family_selected_windows"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["auto_component_family_pruned_by_window_limit"], 24,
        "{report:#}"
    );
    assert_eq!(report["counts"]["checked_windows"], 3, "{report:#}");
    assert_eq!(report["counts"]["unsat_verified"], 3, "{report:#}");
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_family_requires_window_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-component-family-window-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-family-hooks.tsv");
    let out = dir.path().join("component-family-window.json");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t1\t51\t1\t2\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tall-three\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-component-family-windows",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair unbounded component-family window");

    assert!(
        !output.status.success(),
        "unbounded component-family window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--auto-component-family-windows requires --window-limit"),
        "stderr should explain bounded component-family requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_component_window_auto_component_family_rejects_other_window_modes() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-family-window-mixed.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-family-hooks.tsv");
    let work = dir.path().join("work");

    fs::write(&cnf, "p cnf 4 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\ttrue\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t1\t51\t1\t2\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tall-three\n",
        ),
    )
    .expect("write component hooks");

    let explicit_out = dir.path().join("component-family-window-explicit.json");
    let explicit_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--window",
            "manual=2",
            "--auto-component-family-windows",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&explicit_out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair explicit mixed component-family window");
    assert!(
        !explicit_output.status.success(),
        "explicit mixed component-family window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&explicit_output.stdout),
        String::from_utf8_lossy(&explicit_output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&explicit_output.stderr).contains(
            "--auto-component-family-windows cannot be combined with explicit --window entries"
        ),
        "stderr should explain explicit-window exclusion:\n{}",
        String::from_utf8_lossy(&explicit_output.stderr)
    );

    let hitting_out = dir.path().join("component-family-window-hitting.json");
    let hitting_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "component-window",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--radius",
            "0",
            "--auto-component-hitting-windows",
            "--auto-component-family-windows",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&hitting_out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair hitting mixed component-family window");
    assert!(
        !hitting_output.status.success(),
        "hitting mixed component-family window should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&hitting_output.stdout),
        String::from_utf8_lossy(&hitting_output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&hitting_output.stderr).contains(
            "--auto-component-hitting-windows cannot be combined with --auto-component-family-windows"
        ),
        "stderr should explain component auto-window exclusion:\n{}",
        String::from_utf8_lossy(&hitting_output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_audit_validates_original_dimacs() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-sat.cnf");
    let ledger = dir.path().join("assignment.tsv");
    let out = dir.path().join("assignment-audit.json");

    fs::write(&cnf, "p cnf 2 2\n1 2 0\n-1 2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\ttrue\n").expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-audit");

    assert!(
        output.status.success(),
        "assignment-audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read assignment audit JSON"))
            .expect("parse assignment audit JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-assignment-audit/v1",
        "{report:#}"
    );
    assert_eq!(report["residual"]["count"], 0, "{report:#}");
    assert_eq!(
        report["verdict"]["original_dimacs_valid_model"], true,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["model_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );

    let model = dir.path().join("model.out");
    let model_out = dir.path().join("assignment-audit-model.json");
    fs::write(&model, "s SATISFIABLE\nv -1 2 0\n").expect("write DIMACS model");

    let model_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--dimacs-model")
        .arg(&model)
        .arg("--output")
        .arg(&model_out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-audit --dimacs-model");

    assert!(
        model_output.status.success(),
        "DIMACS model audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        model_output.status.code(),
        String::from_utf8_lossy(&model_output.stdout),
        String::from_utf8_lossy(&model_output.stderr)
    );
    let model_report: Value =
        serde_json::from_str(&fs::read_to_string(&model_out).expect("read model audit JSON"))
            .expect("parse model audit JSON");
    assert_eq!(
        model_report["assignment"]["source"]["kind"], "dimacs_model",
        "{model_report:#}"
    );
    assert_eq!(model_report["residual"]["count"], 0, "{model_report:#}");
    assert_eq!(
        model_report["verdict"]["original_dimacs_valid_model"], true,
        "{model_report:#}"
    );

    let flip_file = dir.path().join("flips.tsv");
    let flip_out = dir.path().join("assignment-audit-flip.json");
    fs::write(&flip_file, "original_var\tnote\n2\tbreak-model\n").expect("write flip file");

    let flip_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--flip-file")
        .arg(&flip_file)
        .arg("--output")
        .arg(&flip_out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-audit --flip-file");

    assert!(
        flip_output.status.success(),
        "flip-file audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        flip_output.status.code(),
        String::from_utf8_lossy(&flip_output.stdout),
        String::from_utf8_lossy(&flip_output.stderr)
    );
    let flip_report: Value =
        serde_json::from_str(&fs::read_to_string(&flip_out).expect("read flip audit JSON"))
            .expect("parse flip audit JSON");
    assert_eq!(flip_report["assignment"]["flipped_var_count"], 1);
    assert_eq!(flip_report["residual"]["count"], 1, "{flip_report:#}");
    assert_eq!(
        flip_report["verdict"]["original_dimacs_valid_model"], false,
        "{flip_report:#}"
    );

    let broken_ledger = dir.path().join("broken-assignment.tsv");
    let set_file = dir.path().join("sets.tsv");
    let set_out = dir.path().join("assignment-audit-set.json");
    fs::write(&broken_ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n")
        .expect("write broken ledger");
    fs::write(&set_file, "original_var\tcandidate_value\n2\ttrue\n").expect("write set file");

    let set_output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&broken_ledger)
        .arg("--set-file")
        .arg(&set_file)
        .arg("--output")
        .arg(&set_out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-audit --set-file");

    assert!(
        set_output.status.success(),
        "set-file audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        set_output.status.code(),
        String::from_utf8_lossy(&set_output.stdout),
        String::from_utf8_lossy(&set_output.stderr)
    );
    let set_report: Value =
        serde_json::from_str(&fs::read_to_string(&set_out).expect("read set audit JSON"))
            .expect("parse set audit JSON");
    assert_eq!(set_report["assignment"]["set_var_count"], 1);
    assert_eq!(set_report["residual"]["count"], 0, "{set_report:#}");
    assert_eq!(
        set_report["verdict"]["original_dimacs_valid_model"], true,
        "{set_report:#}"
    );
    assert_eq!(
        set_report["verdict"]["model_output_authority"], false,
        "{set_report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_writes_best_delta() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-search.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("local-search.json");
    let best_set = dir.path().join("local-search-best-set.tsv");

    fs::write(&cnf, "p cnf 2 2\n1 0\n2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args(["--rounds", "2", "--output"])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search");

    assert!(
        output.status.success(),
        "assignment-local-search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read local search JSON"))
            .expect("parse local search JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-assignment-local-search/v1",
        "{report:#}"
    );
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(report["best"]["changed_from_w210_var_count"], 2);
    assert_eq!(
        report["verdict"]["original_dimacs_valid_model"], true,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
    assert!(
        best_set.exists(),
        "local search should write reusable set TSV at {}",
        best_set.display()
    );
    let best_text = fs::read_to_string(&best_set).expect("read best set TSV");
    assert!(
        best_text.contains("1\tfalse\ttrue\ttrue") && best_text.contains("2\tfalse\ttrue\ttrue"),
        "best set TSV should contain both repairs:\n{best_text}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_finds_pair_move() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-pair-search.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("pair-search.json");

    fs::write(&cnf, "p cnf 2 3\n1 2 0\n-1 2 0\n1 -2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--rounds",
            "1",
            "--pair-rounds",
            "1",
            "--candidate-vars",
            "1,2",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search pair mode");

    assert!(
        output.status.success(),
        "pair local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read pair search JSON"))
            .expect("parse pair search JSON");
    assert_eq!(
        report["search"]["rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["pair_rounds"][0]["selected_one_based_vars"],
        serde_json::json!([1, 2]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_finds_group_move() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-group-search.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("group-search.json");

    fs::write(
        &cnf,
        "p cnf 3 7\n1 2 3 0\n-1 2 3 0\n1 -2 3 0\n1 2 -3 0\n-1 -2 3 0\n-1 2 -3 0\n1 -2 -3 0\n",
    )
    .expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--rounds",
            "1",
            "--pair-rounds",
            "1",
            "--group-rounds",
            "1",
            "--group-size",
            "3",
            "--group-window-size",
            "3",
            "--candidate-vars",
            "1,2,3",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search group mode");

    assert!(
        output.status.success(),
        "group local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read group search JSON"))
            .expect("parse group search JSON");
    assert_eq!(
        report["search"]["rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["pair_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["selected_one_based_vars"],
        serde_json::json!([1, 2, 3]),
        "{report:#}"
    );
    assert_eq!(report["search"]["evaluated_group_flips"], 1, "{report:#}");
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_finds_component_family_group_move() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-component-family-search.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-family-hooks.tsv");
    let out = dir.path().join("component-family-search.json");

    fs::write(&cnf, "p cnf 3 3\n1 0\n2 0\n3 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t3\t1 2 3\t3\t1 2 3\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tall-three\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--component-family-rounds",
            "1",
            "--component-family-group-limit",
            "1",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search component-family mode");

    assert!(
        output.status.success(),
        "component-family local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read component-family search JSON"))
            .expect("parse component-family search JSON");
    assert_eq!(
        report["search"]["component_family_rounds_run"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["component_family_group_candidate_windows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["component_family_group_selected_windows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["component_family_groups"][0]["name"], "component-family-c5-v1-v2-v3",
        "{report:#}"
    );
    assert_eq!(
        report["search"]["component_family_group_rounds"][0]["selected_group_name"],
        "component-family-c5-v1-v2-v3",
        "{report:#}"
    );
    assert_eq!(
        report["search"]["component_family_group_rounds"][0]["selected_one_based_vars"],
        serde_json::json!([1, 2, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["complete_original_dimacs_valid_model_found"], true,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_component_family_requires_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-component-family-search-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let component_hooks = dir.path().join("component-family-hooks.tsv");
    let out = dir.path().join("component-family-search.json");

    fs::write(&cnf, "p cnf 3 3\n1 0\n2 0\n3 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t3\t1 2 3\t3\t1 2 3\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tall-three\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--component-family-rounds",
            "1",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search unbounded component-family mode");

    assert!(
        !output.status.success(),
        "component-family local search without limit should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--component-family-rounds requires --component-family-group-limit"),
        "stderr should explain bounded component-family group requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_values_set_required_values() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-values.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let component_hooks = dir.path().join("component-source-hook-targets.tsv");
    let out = dir.path().join("source-frame-values.json");

    fs::write(&cnf, "p cnf 4 4\n1 0\n-2 0\n3 0\n4 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\ttrue\n3\tfalse\n4\ttrue\n",
    )
    .expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r2\t2\t1\t-2\t2\tw210_scc_choice\tscc\tscc_choice\ttrue\tfalse\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r3\t3\t1\t3\t3\tforced_gate_replay_bridge\tbridge\tand_gate_replay\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r4\t4\t1\t4\t4\tw210_frontier\tfrontier\tfrontier\ttrue\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "5\t4\t1 2 3 4\t4\t1 2 3 4\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tset-required-values\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-value-rounds",
            "1",
            "--source-frame-value-limit",
            "1",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search source-frame value mode");

    assert!(
        output.status.success(),
        "source-frame value local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read source-frame value JSON"))
            .expect("parse source-frame value JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_rounds_run"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_candidate_windows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_selected_overlays"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_overlays"][0]["one_based_set_values"],
        serde_json::json!([
            { "var": 1, "value": true },
            { "var": 2, "value": false },
            { "var": 3, "value": true },
            { "var": 4, "value": true }
        ]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_rounds"][0]["selected_one_based_set_values"],
        serde_json::json!([
            { "var": 1, "value": true },
            { "var": 2, "value": false },
            { "var": 3, "value": true },
            { "var": 4, "value": true }
        ]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["complete_original_dimacs_valid_model_found"], true,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_values_reports_conflict_and_no_improvement()
{
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-values-conflict.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let component_hooks = dir.path().join("component-source-hook-targets.tsv");
    let out = dir.path().join("source-frame-values-conflict.json");

    fs::write(&cnf, "p cnf 2 3\n1 0\n-1 0\n2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\ttrue\n2\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\ttrue\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r2\t2\t1\t-1\t1\tforced_gate_replay_bridge\tbridge\tand_gate_replay\ttrue\tfalse\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "1\t2\t1 2\t1\t1\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tconflicting-required-values\n",
            "2\t1\t1\t1\t1\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\talready-satisfied-no-improve\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-value-rounds",
            "1",
            "--source-frame-value-limit",
            "2",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect(
            "spawn ay sat-comp-repair assignment-local-search conflicting source-frame value mode",
        );

    assert!(
        output.status.success(),
        "conflicting source-frame value local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read source-frame value conflict JSON"),
    )
    .expect("parse source-frame value conflict JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_selected_overlays"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_conflicting_overlays"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_overlays"][0]["conflicting_required_values"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_overlays"][0]["conflicting_one_based_vars"],
        serde_json::json!([1]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_value_rounds"][0]["selected_overlay_name"],
        Value::Null,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 0,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_values_requires_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-values-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let component_hooks = dir.path().join("component-source-hook-targets.tsv");
    let out = dir.path().join("source-frame-values-unbounded.json");

    fs::write(&cnf, "p cnf 1 1\n1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");
    fs::write(
        &component_hooks,
        concat!(
            "component_id\tclause_count\tclause_ids\tmin_variable_hitting_set_size\trepresentative_minimal_vars\tcovered_real_source_families\tdiagnostic_missing_literal_rows\tsource_frame_class\tconstruction_action\n",
            "1\t1\t1\t1\t1\tforced_gate_replay_bridge w210_frontier w210_scc_choice\t0\tbridge_source_frame\tset-required-values\n",
        ),
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-value-rounds",
            "1",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect(
            "spawn ay sat-comp-repair assignment-local-search unbounded source-frame value mode",
        );

    assert!(
        !output.status.success(),
        "source-frame value local search without limit should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--source-frame-value-rounds requires --source-frame-value-limit"),
        "stderr should explain bounded source-frame value requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_finds_zero_residual_diagnostic() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-choice.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let out = dir.path().join("source-frame-choice.json");

    fs::write(&cnf, "p cnf 3 3\n1 2 0\n-1 0\n3 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1_bad_side_effect\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r1_good_choice\t1\t2\t2\t2\tw210_scc_choice\tscc\tscc_choice\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r3_good_choice\t3\t1\t3\t3\tforced_gate_replay_bridge\tbridge\tand_gate_replay\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "4",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search source-frame choice mode");

    assert!(
        output.status.success(),
        "source-frame choice local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read source-frame choice JSON"))
            .expect("parse source-frame choice JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_clauses_with_choices"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_source_frame_row_ids"],
        serde_json::json!(["r1_good_choice", "r3_good_choice"]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_one_based_set_values"],
        serde_json::json!([{ "var": 2, "value": true }, { "var": 3, "value": true }]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 2,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_requires_limit() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-choice-unbounded.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let out = dir.path().join("source-frame-choice-unbounded.json");

    fs::write(&cnf, "p cnf 1 1\n1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect(
            "spawn ay sat-comp-repair assignment-local-search unbounded source-frame choice mode",
        );

    assert!(
        !output.status.success(),
        "source-frame choice local search without limit should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--source-frame-choice-rounds requires --source-frame-choice-limit"),
        "stderr should explain bounded source-frame choice requirement:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_uses_current_residual_choices() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-source-frame-choice-current-residual.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let out = dir.path().join("source-frame-choice-current-residual.json");

    fs::write(&cnf, "p cnf 2 2\n1 0\n-1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r2_non_residual\t2\t1\t-1\t1\tw210_scc_choice\tscc\tscc_choice\tfalse\tfalse\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "4",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect(
            "spawn ay sat-comp-repair assignment-local-search current-residual source-frame choice mode",
        );

    assert!(
        output.status.success(),
        "current-residual source-frame choice local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read source-frame choice current-residual JSON"),
    )
    .expect("parse source-frame choice current-residual JSON");
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_clauses_with_choices"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["beam_final_width"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["top_candidates"][0]
            ["source_frame_row_ids"],
        serde_json::json!([]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

fn write_tiny_dynamic_source_frame_choice_fixture(dir: &Path) -> (PathBuf, PathBuf, PathBuf) {
    let cnf = dir.join("tiny-dynamic-source-frame-choice.cnf");
    let ledger = dir.join("w210.tsv");
    let source_rows = dir.join("source-frame-input-rows.tsv");
    fs::write(&cnf, "p cnf 2 3\n1 0\n-1 2 0\n2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1_neutral_introduces_c2\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
            "r2_dynamic_clears_c2_and_c3\t2\t2\t2\t2\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");
    (cnf, ledger, source_rows)
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_dynamic_default_skips_neutral_move()
{
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, source_rows) = write_tiny_dynamic_source_frame_choice_fixture(dir.path());
    let out = dir.path().join("dynamic-source-frame-choice-default.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "2",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "4",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search dynamic default mode");

    assert!(
        output.status.success(),
        "default source-frame choice search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read default dynamic source-frame choice JSON"),
    )
    .expect("parse default dynamic source-frame choice JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_one_based_clause_ids"],
        serde_json::json!([1, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_dynamic_residual_choices"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_accept_neutral"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds_run"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_source_frame_row_ids"],
        Value::Null,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["improved"], false,
        "{report:#}"
    );
    let neutral_candidate = report["search"]["source_frame_choice_rounds"][0]["top_candidates"]
        .as_array()
        .expect("top candidates")
        .iter()
        .find(|candidate| {
            candidate["source_frame_row_ids"] == serde_json::json!(["r1_neutral_introduces_c2"])
        })
        .expect("neutral source-frame candidate should be reported");
    assert_eq!(
        neutral_candidate["side_effect_summary"]["introduced_residual_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_one_based_clause_ids"],
        serde_json::json!([1, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 0,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_dynamic_applies_neutral_and_regenerates_choices(
) {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, source_rows) = write_tiny_dynamic_source_frame_choice_fixture(dir.path());
    let out = dir.path().join("dynamic-source-frame-choice-opt-in.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "2",
            "--source-frame-choice-limit",
            "1",
            "--source-frame-choice-beam-width",
            "4",
            "--source-frame-choice-dynamic-residual-choices",
            "--source-frame-choice-accept-neutral",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search dynamic residual mode");

    assert!(
        output.status.success(),
        "dynamic residual source-frame choice search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read dynamic source-frame choice JSON"),
    )
    .expect("parse dynamic source-frame choice JSON");
    assert_eq!(
        report["search"]["source_frame_choice_dynamic_residual_choices"], true,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_accept_neutral"], true,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds_run"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_source_frame_row_ids"],
        serde_json::json!(["r1_neutral_introduces_c2"]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["applied_non_worsening"], true,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]
            ["ending_residual_falsified_one_based_clause_ids"],
        serde_json::json!([2, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["side_effect_summary"]
            ["introduced_residual_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][1]
            ["choices_regenerated_from_current_residual"],
        true,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][1]
            ["starting_residual_falsified_one_based_clause_ids"],
        serde_json::json!([2, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][1]["selected_source_frame_row_ids"],
        serde_json::json!(["r2_dynamic_clears_c2_and_c3"]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][1]["improved"], true,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 2,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_dynamic_validates_options() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, source_rows) = write_tiny_dynamic_source_frame_choice_fixture(dir.path());
    let out = dir.path().join("dynamic-source-frame-choice-invalid.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-accept-neutral",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search invalid dynamic mode");

    assert!(
        !output.status.success(),
        "neutral-accepting source-frame choice mode without source-frame choice rounds should fail; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--source-frame-choice-accept-neutral")
            && stderr.contains("--source-frame-choice-rounds"),
        "stderr should explain dynamic mode option requirements; stderr:\n{stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_uses_remaining_clause_ledger() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-source-frame-choice-remaining-ledger.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let remaining = dir.path().join("remaining-clause-value-ledger.tsv");
    let out = dir.path().join("source-frame-choice-remaining-ledger.json");

    fs::write(&cnf, "p cnf 3 3\n1 2 0\n-1 0\n3 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &source_rows,
        "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
    )
    .expect("write empty source frame rows");
    fs::write(
        &remaining,
        concat!(
            "clause_index_1_based\tclassification\tvariables\tsource_counts\tfrontier_vars\tcyclic_scc_vars\tforced_gate_vars\tactive_in_cegar_best\tall_literals_false_under_best_assignment\tliteral_values\tclause\n",
            "1\ttest\t1 2\t{}\t2\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":1,\"\"literal_value\"\":false,\"\"source\"\":\"\"forced_gate_output_cegar_checked\"\",\"\"var\"\":1,\"\"var_value\"\":false},{\"\"lit\"\":2,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":2,\"\"var_value\"\":false}]\"\t1 2\n",
            "3\ttest\t3\t{}\t3\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":3,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":3,\"\"var_value\"\":false}]\"\t3\n",
        ),
    )
    .expect("write remaining clause ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--source-frame-choice-remaining-clause-ledger")
        .arg(&remaining)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "4",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search remaining-clause choice mode");

    assert!(
        output.status.success(),
        "remaining-clause choice local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read remaining-clause choice JSON"))
            .expect("parse remaining-clause choice JSON");
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_rows_seen"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_choice_rows"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_one_based_set_values"],
        serde_json::json!([{ "var": 2, "value": true }, { "var": 3, "value": true }]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 2,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_can_skip_side_effect_choices() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-source-frame-choice-skip-side-effect.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let remaining = dir.path().join("remaining-clause-value-ledger.tsv");
    let out = dir.path().join("source-frame-choice-skip-side-effect.json");

    fs::write(&cnf, "p cnf 2 4\n1 0\n2 0\n-1 0\n-1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
    )
    .expect("write empty source frame rows");
    fs::write(
        &remaining,
        concat!(
            "clause_index_1_based\tclassification\tvariables\tsource_counts\tfrontier_vars\tcyclic_scc_vars\tforced_gate_vars\tactive_in_cegar_best\tall_literals_false_under_best_assignment\tliteral_values\tclause\n",
            "1\ttest\t1\t{}\t1\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":1,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":1,\"\"var_value\"\":false}]\"\t1\n",
            "2\ttest\t2\t{}\t2\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":2,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":2,\"\"var_value\"\":false}]\"\t2\n",
        ),
    )
    .expect("write remaining clause ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--source-frame-choice-current-remaining-clause-value-ledger")
        .arg(&remaining)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "8",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search skip source-frame choice mode");

    assert!(
        output.status.success(),
        "skip-enabled source-frame choice local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read skip source-frame choice JSON"),
    )
    .expect("parse skip source-frame choice JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_choice_rows"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_source_frame_row_ids"],
        serde_json::json!(["remaining_clause_value:clause_2:lit_1:var_2"]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["selected_one_based_set_values"],
        serde_json::json!([{ "var": 2, "value": true }]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 1,
        "{report:#}"
    );
    let top_candidates = report["search"]["source_frame_choice_rounds"][0]["top_candidates"]
        .as_array()
        .expect("top candidates");
    assert_eq!(
        top_candidates[0]["side_effect_summary"]["relative_to"], "round_start_assignment",
        "{report:#}"
    );
    assert_eq!(
        top_candidates[0]["side_effect_summary"]["authority"], "diagnostic_only",
        "{report:#}"
    );
    assert_eq!(
        top_candidates[0]["side_effect_summary"]
            ["cleared_round_start_residual_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        top_candidates[0]["side_effect_summary"]["introduced_residual_one_based_clause_ids"],
        serde_json::json!([]),
        "{report:#}"
    );
    assert_eq!(
        top_candidates[0]["side_effect_summary"]["net_residual_delta"],
        serde_json::json!(-1),
        "{report:#}"
    );
    assert_eq!(
        top_candidates[0]["side_effect_summary"]["affected_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    let side_effect_candidate = top_candidates
        .iter()
        .find(|candidate| {
            candidate["source_frame_row_ids"]
                == serde_json::json!(["remaining_clause_value:clause_1:lit_1:var_1"])
        })
        .expect("side-effect candidate should be reported");
    assert_eq!(
        side_effect_candidate["side_effect_summary"]
            ["cleared_round_start_residual_one_based_clause_ids"],
        serde_json::json!([1]),
        "{report:#}"
    );
    assert_eq!(
        side_effect_candidate["side_effect_summary"]
            ["retained_baseline_residual_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        side_effect_candidate["side_effect_summary"]["introduced_residual_one_based_clause_ids"],
        serde_json::json!([3, 4]),
        "{report:#}"
    );
    assert_eq!(
        side_effect_candidate["side_effect_summary"]["net_residual_delta"],
        serde_json::json!(1),
        "{report:#}"
    );
    assert_eq!(
        side_effect_candidate["side_effect_summary"]["affected_one_based_clause_ids"],
        serde_json::json!([1, 3, 4]),
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_frontier_writes_diagnostic_artifacts() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-introduced-backfill.cnf");
    let local_search = dir.path().join("assignment-local-search.json");
    let out = dir.path().join("introduced-clause-backfill-frontier.json");
    let tsv = dir.path().join("introduced-clause-backfill-frontier.tsv");

    let cnf_text = "p cnf 4 4\n1 2 0\n-1 3 0\n-2 3 4 0\n-4 0\n";
    fs::write(&cnf, cnf_text).expect("write CNF");
    let local_search_report = serde_json::json!({
        "schema": "ay.satcomp-circuit-assignment-local-search/v1",
        "source": {
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
            "note": "test fixture diagnostic-only assignment-local-search report",
        },
        "authority": diagnostic_authority_json(),
        "input": {
            "sha256": sha256_hex(cnf_text.as_bytes()),
            "num_vars": 4,
            "num_clauses": 4,
        },
        "search": {
            "source_frame_choice_rounds": [
                {
                    "round": 1,
                    "top_candidates": [
                        {
                            "source_frame_row_ids": [
                                "remaining_clause_value:clause_1:lit_1:var_1"
                            ],
                            "one_based_clause_ids": [1],
                            "one_based_set_values": [
                                { "var": 1, "value": true },
                                { "var": 2, "value": false }
                            ],
                            "residual_falsified_clause_count": 3,
                            "residual_falsified_one_based_clause_ids": [1, 3, 4],
                            "side_effect_summary": {
                                "authority": "diagnostic_only",
                                "cleared_round_start_residual_one_based_clause_ids": [1],
                                "introduced_residual_count": 3,
                                "affected_one_based_clause_ids": [1, 3, 4],
                                "net_residual_delta": 2,
                                "introduced_residual_one_based_clause_ids": [3, 4, 3]
                            }
                        },
                        {
                            "source_frame_row_ids": [
                                "remaining_clause_value:clause_2:lit_1:var_3"
                            ],
                            "one_based_clause_ids": [2],
                            "one_based_set_values": [
                                { "var": 3, "value": true }
                            ],
                            "residual_falsified_clause_count": 1,
                            "residual_falsified_one_based_clause_ids": [4],
                            "side_effect_summary": {
                                "authority": "diagnostic_only",
                                "cleared_round_start_residual_one_based_clause_ids": [2],
                                "introduced_residual_count": 1,
                                "affected_one_based_clause_ids": [2, 4],
                                "net_residual_delta": 0,
                                "introduced_residual_one_based_clause_ids": [4]
                            }
                        }
                    ]
                }
            ]
        },
        "verdict": {
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false
        }
    });
    fs::write(
        &local_search,
        serde_json::to_string_pretty(&local_search_report).expect("serialize local search report"),
    )
    .expect("write local search report");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-frontier",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--assignment-local-search-report")
        .arg(&local_search)
        .arg("--output")
        .arg(&out)
        .arg("--tsv-output")
        .arg(&tsv)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-frontier");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-frontier should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read introduced-clause backfill JSON"),
    )
    .expect("parse introduced-clause backfill JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
        "{report:#}"
    );
    assert_eq!(report["input"]["num_vars"], 4, "{report:#}");
    assert_eq!(report["input"]["num_clauses"], 4, "{report:#}");
    assert_eq!(
        report["introduced_clauses"]["source_frame_choice_rounds_seen"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["top_candidates_seen"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["top_candidates_with_side_effect_summary"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["top_candidates_with_introductions"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["seen_clause_references"], 4,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["deduped_duplicate_clause_references"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["unique_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["one_based_clause_ids"],
        serde_json::json!([3, 4]),
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["frontier_clause_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["frontier_clause_one_based_vars"],
        serde_json::json!([2, 3, 4]),
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["candidate_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clauses"]["candidate_one_based_vars"],
        serde_json::json!([1, 2, 3]),
        "{report:#}"
    );
    let clauses = report["introduced_clauses"]["clauses"]
        .as_array()
        .expect("frontier clauses");
    assert_eq!(clauses.len(), 2, "{report:#}");
    assert_eq!(clauses[0]["one_based_clause_id"], 3, "{report:#}");
    assert_eq!(
        clauses[0]["original_clause_lits"],
        serde_json::json!([-2, 3, 4]),
        "{report:#}"
    );
    assert_eq!(
        clauses[0]["original_clause_one_based_vars"],
        serde_json::json!([2, 3, 4]),
        "{report:#}"
    );
    assert_eq!(
        clauses[0]["candidate_one_based_vars"],
        serde_json::json!([1, 2]),
        "{report:#}"
    );
    assert_eq!(clauses[0]["occurrence_count"], 2, "{report:#}");
    assert_eq!(
        clauses[0]["authority"]["classification"], "diagnostic_only",
        "{report:#}"
    );
    assert_eq!(clauses[1]["one_based_clause_id"], 4, "{report:#}");
    assert_eq!(
        clauses[1]["original_clause_lits"],
        serde_json::json!([-4]),
        "{report:#}"
    );
    assert_eq!(
        clauses[1]["original_clause_one_based_vars"],
        serde_json::json!([4]),
        "{report:#}"
    );
    assert_eq!(
        clauses[1]["candidate_one_based_vars"],
        serde_json::json!([1, 2, 3]),
        "{report:#}"
    );
    assert_eq!(clauses[1]["occurrence_count"], 2, "{report:#}");
    assert_eq!(
        clauses[1]["authority"]["classification"], "diagnostic_only",
        "{report:#}"
    );
    assert_eq!(report["authority"]["classification"], "diagnostic_only");
    assert_eq!(report["authority"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["authority"]["sat_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["model_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["proof_output_authority"], false,
        "{report:#}"
    );
    assert_diagnostic_only(&report);

    let tsv_text = fs::read_to_string(&tsv).expect("read introduced-clause backfill TSV");
    let tsv_lines: Vec<_> = tsv_text.lines().collect();
    assert_eq!(
        tsv_lines,
        vec![
            "one_based_clause_id\toriginal_clause_lits\toriginal_clause_vars\tcandidate_one_based_vars",
            "3\t-2 3 4\t2 3 4\t1 2",
            "4\t-4\t4\t1 2 3",
        ],
        "introduced-clause backfill TSV should have one deduped row per introduced clause:\n{tsv_text}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_frontier_rejects_untrusted_reports() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-introduced-backfill-reject.cnf");
    let out = dir.path().join("introduced-clause-backfill-frontier.json");
    let cnf_text = "p cnf 2 2\n1 0\n-2 0\n";
    fs::write(&cnf, cnf_text).expect("write CNF");

    let base_report = serde_json::json!({
        "schema": "ay.satcomp-circuit-assignment-local-search/v1",
        "source": {
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
            "note": "test fixture diagnostic-only assignment-local-search report",
        },
        "authority": diagnostic_authority_json(),
        "input": {
            "sha256": sha256_hex(cnf_text.as_bytes()),
            "num_vars": 2,
            "num_clauses": 2,
        },
        "search": {
            "source_frame_choice_rounds": [
                {
                    "round": 1,
                    "top_candidates": [
                        {
                            "source_frame_row_ids": ["row-1"],
                            "one_based_clause_ids": [1],
                            "one_based_set_values": [{ "var": 1, "value": true }],
                            "side_effect_summary": {
                                "authority": "diagnostic_only",
                                "cleared_round_start_residual_one_based_clause_ids": [1],
                                "affected_one_based_clause_ids": [1],
                                "introduced_residual_one_based_clause_ids": [2]
                            }
                        }
                    ]
                }
            ]
        },
        "verdict": {
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false
        }
    });

    let mut cases = Vec::new();

    let mut bad_authority = base_report.clone();
    bad_authority["verdict"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-authority",
        bad_authority,
        "verdict.route_admitted must be false",
    ));

    let mut bad_report_authority = base_report.clone();
    bad_report_authority["authority"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-report-authority",
        bad_report_authority,
        "authority.route_admitted must be false",
    ));

    let mut stale_report_head = base_report.clone();
    stale_report_head["source"]["repo_head"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-report-head", stale_report_head, "source.repo_head"));

    let mut stale_report_build = base_report.clone();
    stale_report_build["source"]["ay_build"]["commit"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-report-build", stale_report_build, "ay_build.commit"));

    let mut bad_sha = base_report.clone();
    bad_sha["input"]["sha256"] = serde_json::json!("0".repeat(64));
    cases.push(("bad-sha", bad_sha, "input.sha256"));

    let mut bad_clause = base_report.clone();
    bad_clause["search"]["source_frame_choice_rounds"][0]["top_candidates"][0]
        ["side_effect_summary"]["introduced_residual_one_based_clause_ids"] =
        serde_json::json!([0]);
    cases.push(("bad-clause", bad_clause, "out of range"));

    let mut bad_summary_authority = base_report;
    bad_summary_authority["search"]["source_frame_choice_rounds"][0]["top_candidates"][0]
        ["side_effect_summary"]["authority"] = serde_json::json!("route_authorized");
    cases.push((
        "bad-summary-authority",
        bad_summary_authority,
        "diagnostic_only",
    ));

    for (case, report, expected_stderr) in cases {
        let local_search = dir.path().join(format!("{case}.json"));
        fs::write(
            &local_search,
            serde_json::to_string_pretty(&report).expect("serialize rejection report"),
        )
        .expect("write rejection report");

        let output = Command::new(ay())
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "introduced-clause-backfill-frontier",
                "--target-cnf",
            ])
            .arg(&cnf)
            .arg("--assignment-local-search-report")
            .arg(&local_search)
            .arg("--output")
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect("spawn ay sat-comp-repair introduced-clause-backfill-frontier rejection");

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
    }
}

fn diagnostic_authority_json() -> Value {
    serde_json::json!({
        "classification": "diagnostic_only",
        "route_admitted": false,
        "sat_output_authority": false,
        "model_output_authority": false,
        "proof_output_authority": false,
        "solver_verdict_authority": false,
        "sat_comp_progress_claim": false,
    })
}

fn tiny_residual_side_effect_report(cnf_text: &str) -> Value {
    serde_json::json!({
        "schema": "ay.satcomp-circuit-assignment-local-search/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": {
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
            "note": "test fixture W210 side-effect report",
        },
        "authority": diagnostic_authority_json(),
        "input": {
            "path": "tiny-residual-side-effect.cnf",
            "sha256": sha256_hex(cnf_text.as_bytes()),
            "num_vars": 4,
            "num_clauses": 4,
        },
        "baseline_w210": {
            "residual_falsified_clause_count": 3,
            "residual_falsified_one_based_clause_ids": [1, 2, 3],
        },
        "search": {
            "source_frame_choice_rounds": [
                {
                    "round": 1,
                    "top_candidates": [
                        {
                            "source_frame_row_ids": ["row-clear-1"],
                            "one_based_clause_ids": [1],
                            "one_based_set_values": [{ "var": 1, "value": true }],
                            "residual_falsified_clause_count": 3,
                            "residual_falsified_one_based_clause_ids": [2, 3, 4],
                            "side_effect_summary": {
                                "authority": "diagnostic_only",
                                "baseline_residual_falsified_clause_count": 3,
                                "candidate_residual_falsified_clause_count": 3,
                                "net_residual_delta": 0,
                                "relative_to": "round_start_assignment",
                                "affected_clause_count": 2,
                                "affected_one_based_clause_ids": [1, 4],
                                "cleared_round_start_residual_count": 1,
                                "cleared_round_start_residual_one_based_clause_ids": [1],
                                "retained_baseline_residual_count": 2,
                                "retained_baseline_residual_one_based_clause_ids": [2, 3],
                                "introduced_residual_count": 1,
                                "introduced_residual_one_based_clause_ids": [4],
                            },
                        },
                        {
                            "source_frame_row_ids": ["row-clear-2"],
                            "one_based_clause_ids": [2],
                            "one_based_set_values": [{ "var": 2, "value": false }],
                            "residual_falsified_clause_count": 2,
                            "residual_falsified_one_based_clause_ids": [1, 3],
                            "side_effect_summary": {
                                "authority": "diagnostic_only",
                                "baseline_residual_falsified_clause_count": 3,
                                "candidate_residual_falsified_clause_count": 2,
                                "net_residual_delta": -1,
                                "relative_to": "round_start_assignment",
                                "affected_clause_count": 1,
                                "affected_one_based_clause_ids": [2],
                                "cleared_round_start_residual_count": 1,
                                "cleared_round_start_residual_one_based_clause_ids": [2],
                                "retained_baseline_residual_count": 2,
                                "retained_baseline_residual_one_based_clause_ids": [1, 3],
                                "introduced_residual_count": 0,
                                "introduced_residual_one_based_clause_ids": [],
                            },
                        },
                    ],
                },
            ],
        },
        "best": {
            "residual_falsified_clause_count": 3,
            "residual_falsified_one_based_clause_ids": [1, 2, 3],
            "original_dimacs_valid_model": false,
        },
        "verdict": {
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
    })
}

fn tiny_residual_side_effect_frontier(cnf_text: &str, side_effect_report_sha256: &str) -> Value {
    let authority = diagnostic_authority_json();
    serde_json::json!({
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": {
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
            "note": "test fixture current derived frontier report",
        },
        "input": {
            "path": "tiny-residual-side-effect.cnf",
            "sha256": sha256_hex(cnf_text.as_bytes()),
            "num_vars": 4,
            "num_clauses": 4,
        },
        "assignment_local_search_report": {
            "path": "tiny-side-effect.json",
            "sha256": side_effect_report_sha256,
            "schema": "ay.satcomp-circuit-assignment-local-search/v1",
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
        },
        "introduced_clauses": {
            "unique_introduced_clause_count": 1,
            "unique_introduced_one_based_clause_ids": [4],
            "clauses": [
                {
                    "one_based_clause_id": 4,
                    "original_clause_lits": [4],
                    "original_clause_one_based_vars": [4],
                    "candidate_one_based_vars": [1],
                    "source_frame_row_id_samples": ["row-clear-1"],
                    "occurrence_count": 1,
                    "authority": authority,
                },
            ],
        },
        "frontier": {
            "unique_introduced_clause_count": 1,
            "unique_introduced_one_based_clause_ids": [4],
        },
        "authority": authority,
        "verdict": {
            "diagnostic_only": true,
            "introduced_clause_frontier_recovered": true,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
    })
}

fn write_tiny_frontier_materializer_fixture(dir: &Path) -> (PathBuf, PathBuf, PathBuf, PathBuf) {
    let cnf = dir.join("tiny-frontier-materializer.cnf");
    let ledger = dir.join("w210.tsv");
    let side_effect = dir.join("tiny-side-effect.json");
    let frontier = dir.join("tiny-frontier.json");
    let cnf_text = "p cnf 4 4\n1 0\n-2 0\n3 0\n-4 0\n";
    fs::write(&cnf, cnf_text).expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\ttrue\n3\tfalse\n4\tfalse\n",
    )
    .expect("write W210 ledger");

    let side_effect_report = tiny_residual_side_effect_report(cnf_text);
    fs::write(
        &side_effect,
        serde_json::to_string_pretty(&side_effect_report).expect("serialize side-effect report"),
    )
    .expect("write side-effect report");
    let side_effect_sha = sha256_hex(
        fs::read_to_string(&side_effect)
            .expect("read side-effect report")
            .as_bytes(),
    );
    let mut frontier_report = tiny_residual_side_effect_frontier(cnf_text, &side_effect_sha);
    frontier_report["introduced_clauses"]["clauses"][0]["original_clause_lits"] =
        serde_json::json!([-4]);
    frontier_report["introduced_clauses"]["clauses"][0]["candidate_one_based_vars"] =
        serde_json::json!([4]);
    fs::write(
        &frontier,
        serde_json::to_string_pretty(&frontier_report).expect("serialize frontier report"),
    )
    .expect("write frontier report");
    (cnf, ledger, side_effect, frontier)
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_residual_side_effect_backbone_writes_diagnostic_report() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-residual-side-effect.cnf");
    let side_effect = dir.path().join("tiny-side-effect.json");
    let frontier = dir.path().join("tiny-frontier.json");
    let out = dir.path().join("residual-side-effect-backbone.json");
    let cnf_text = "p cnf 4 4\n1 0\n-2 0\n3 0\n4 0\n";
    fs::write(&cnf, cnf_text).expect("write CNF");
    let side_effect_report = tiny_residual_side_effect_report(cnf_text);
    fs::write(
        &side_effect,
        serde_json::to_string_pretty(&side_effect_report).expect("serialize side-effect report"),
    )
    .expect("write side-effect report");
    let side_effect_sha = sha256_hex(
        fs::read_to_string(&side_effect)
            .expect("read side-effect report")
            .as_bytes(),
    );
    fs::write(
        &frontier,
        serde_json::to_string_pretty(&tiny_residual_side_effect_frontier(
            cnf_text,
            &side_effect_sha,
        ))
        .expect("serialize frontier report"),
    )
    .expect("write frontier report");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "residual-side-effect-backbone",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--side-effect-report")
        .arg(&side_effect)
        .arg("--frontier-report")
        .arg(&frontier)
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair residual-side-effect-backbone");

    assert!(
        output.status.success(),
        "residual-side-effect-backbone should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read backbone JSON"))
            .expect("parse backbone JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-residual-side-effect-backbone/v1",
        "{report:#}"
    );
    assert!(
        report["source"]["ay_build"]["stamp"]
            .as_str()
            .is_some_and(|stamp| !stamp.is_empty()),
        "diagnostic reports should expose compiled binary provenance: {report:#}"
    );
    assert!(
        report["source"]["ay_build"]["commit"]
            .as_str()
            .is_some_and(|commit| !commit.is_empty()),
        "diagnostic reports should expose compiled binary commit: {report:#}"
    );
    assert_eq!(report["counts"]["anchor_candidate_count"], 2, "{report:#}");
    assert_eq!(report["counts"]["anchored_residual_count"], 2, "{report:#}");
    assert_eq!(
        report["counts"]["uncovered_residual_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["uncovered_residuals"]["one_based_clause_ids"],
        serde_json::json!([3]),
        "{report:#}"
    );
    assert_eq!(
        report["side_effects"]["unique_introduced_residual_one_based_clause_ids"],
        serde_json::json!([4]),
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clause_backfill_frontier"]
            ["side_effect_introduced_covered_one_based_clause_ids"],
        serde_json::json!([4]),
        "{report:#}"
    );
    assert_eq!(
        report["anchors"][0]["frontier_uncovered_introduced_one_based_clause_ids"],
        serde_json::json!([]),
        "{report:#}"
    );
    assert_eq!(
        report["side_effect_report"]["repo_head_matches_current"], true,
        "{report:#}"
    );
    assert_eq!(
        report["side_effect_report"]["ay_build"]["commit"],
        current_ay_build_json()["commit"],
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_frontier_assisted_model_materializer_writes_diagnostic_report() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, side_effect, frontier) = write_tiny_frontier_materializer_fixture(dir.path());
    let out = dir.path().join("frontier-assisted-model-materializer.json");
    let work = dir.path().join("frontier-materializer-work");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "frontier-assisted-model-materializer",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--side-effect-report")
        .arg(&side_effect)
        .arg("--frontier-report")
        .arg(&frontier)
        .args([
            "--target-residual-clause",
            "3",
            "--radius",
            "0",
            "--frontier-candidate-limit",
            "4",
            "--window-size",
            "1",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .arg("--work-dir")
        .arg(&work)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair frontier-assisted-model-materializer");

    assert!(
        output.status.success(),
        "frontier-assisted-model-materializer should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read frontier materializer JSON"))
            .expect("parse frontier materializer JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-frontier-assisted-model-materializer/v1",
        "{report:#}"
    );
    assert_eq!(
        report["target_residual"]["one_based_clause_id"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["target_residual"]["covered_by_side_effect_anchor"], false,
        "{report:#}"
    );
    assert_eq!(
        report["materializer_definition"]["selected_frontier_one_based_vars"],
        serde_json::json!([4]),
        "{report:#}"
    );
    assert_eq!(
        report["materializer_definition"]["selected_window_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["sat_valid_original_model"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["complete_original_dimacs_valid_model_found"], true,
        "{report:#}"
    );
    assert_eq!(
        report["frontier_ledger"]["rows"][0]["outside_radius"], true,
        "{report:#}"
    );
    assert_eq!(report["authority"]["classification"], "diagnostic_only");
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_frontier_assisted_model_materializer_rejects_anchored_target() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, side_effect, frontier) = write_tiny_frontier_materializer_fixture(dir.path());
    let out = dir
        .path()
        .join("frontier-assisted-model-materializer-anchored.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "frontier-assisted-model-materializer",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--side-effect-report")
        .arg(&side_effect)
        .arg("--frontier-report")
        .arg(&frontier)
        .args([
            "--target-residual-clause",
            "1",
            "--radius",
            "0",
            "--window-size",
            "1",
            "--window-limit",
            "1",
            "--timeout-sec",
            "10",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair frontier-assisted-model-materializer rejection");

    assert!(
        !output.status.success(),
        "anchored target should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("already has diagnostic anchors"),
        "stderr should explain anchored-target rejection:\n{stderr}"
    );
    assert!(
        !out.exists(),
        "anchored-target rejection must not write an authority-bearing report"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_frontier_assisted_model_materializer_rejects_untrusted_inputs() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, side_effect, frontier) = write_tiny_frontier_materializer_fixture(dir.path());
    let base_side_effect: Value = serde_json::from_str(
        &fs::read_to_string(&side_effect).expect("read base side-effect report"),
    )
    .expect("parse base side-effect report");
    let base_frontier: Value =
        serde_json::from_str(&fs::read_to_string(&frontier).expect("read base frontier report"))
            .expect("parse base frontier report");

    let mut cases: Vec<(&str, Value, Value, &str)> = Vec::new();

    let mut stale_side_effect_stamp = base_side_effect.clone();
    stale_side_effect_stamp["source"]["ay_build"]["stamp"] = serde_json::json!("stale-stamp");
    cases.push((
        "stale-side-effect-stamp",
        stale_side_effect_stamp,
        base_frontier.clone(),
        "ay_build.stamp",
    ));

    let mut bad_side_effect_authority = base_side_effect.clone();
    bad_side_effect_authority["verdict"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-side-effect-verdict-authority",
        bad_side_effect_authority,
        base_frontier.clone(),
        "verdict.route_admitted must be false",
    ));

    let mut bad_side_effect_report_authority = base_side_effect.clone();
    bad_side_effect_report_authority["authority"]["model_output_authority"] =
        serde_json::json!(true);
    cases.push((
        "bad-side-effect-report-authority",
        bad_side_effect_report_authority,
        base_frontier.clone(),
        "authority.model_output_authority must be false",
    ));

    let mut bad_side_effect_sha = base_side_effect.clone();
    bad_side_effect_sha["input"]["sha256"] = serde_json::json!("0".repeat(64));
    cases.push((
        "bad-side-effect-sha",
        bad_side_effect_sha,
        base_frontier.clone(),
        "input.sha256",
    ));

    let mut stale_frontier_stamp = base_frontier.clone();
    stale_frontier_stamp["source"]["ay_build"]["stamp"] = serde_json::json!("stale-stamp");
    cases.push((
        "stale-frontier-stamp",
        base_side_effect.clone(),
        stale_frontier_stamp,
        "ay_build.stamp",
    ));

    let mut stale_frontier_upstream_stamp = base_frontier.clone();
    stale_frontier_upstream_stamp["assignment_local_search_report"]["ay_build"]["stamp"] =
        serde_json::json!("stale-stamp");
    cases.push((
        "stale-frontier-upstream-stamp",
        base_side_effect.clone(),
        stale_frontier_upstream_stamp,
        "ay_build.stamp",
    ));

    let mut bad_frontier_authority = base_frontier.clone();
    bad_frontier_authority["authority"]["proof_output_authority"] = serde_json::json!(true);
    cases.push((
        "bad-frontier-authority",
        base_side_effect.clone(),
        bad_frontier_authority,
        "authority.proof_output_authority must be false",
    ));

    let mut bad_frontier_verdict_authority = base_frontier;
    bad_frontier_verdict_authority["verdict"]["sat_comp_progress_claim"] = serde_json::json!(true);
    cases.push((
        "bad-frontier-verdict-authority",
        base_side_effect,
        bad_frontier_verdict_authority,
        "verdict.sat_comp_progress_claim must be false",
    ));

    for (case, side_effect_report, frontier_report, expected_stderr) in cases {
        let case_side_effect = dir.path().join(format!("{case}-side-effect.json"));
        let case_frontier = dir.path().join(format!("{case}-frontier.json"));
        let out = dir.path().join(format!("{case}-materializer.json"));
        fs::write(
            &case_side_effect,
            serde_json::to_string_pretty(&side_effect_report)
                .expect("serialize rejection side-effect report"),
        )
        .expect("write rejection side-effect report");
        fs::write(
            &case_frontier,
            serde_json::to_string_pretty(&frontier_report)
                .expect("serialize rejection frontier report"),
        )
        .expect("write rejection frontier report");

        let output = Command::new(ay())
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "frontier-assisted-model-materializer",
                "--target-cnf",
            ])
            .arg(&cnf)
            .arg("--w210-ledger")
            .arg(&ledger)
            .arg("--side-effect-report")
            .arg(&case_side_effect)
            .arg("--frontier-report")
            .arg(&case_frontier)
            .args([
                "--target-residual-clause",
                "3",
                "--radius",
                "0",
                "--window-size",
                "1",
                "--window-limit",
                "1",
                "--timeout-sec",
                "10",
                "--output",
            ])
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect("spawn ay sat-comp-repair frontier-assisted-model-materializer rejection");

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
        assert!(
            !out.exists(),
            "{case} rejection must not write a materializer report"
        );
    }
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_residual_side_effect_backbone_rejects_untrusted_inputs() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-residual-side-effect-reject.cnf");
    let out = dir.path().join("residual-side-effect-backbone.json");
    let cnf_text = "p cnf 4 4\n1 0\n-2 0\n3 0\n4 0\n";
    fs::write(&cnf, cnf_text).expect("write CNF");
    let base_report = tiny_residual_side_effect_report(cnf_text);

    let mut cases: Vec<(&str, Value, Option<Value>, &str)> = Vec::new();

    let mut bad_authority = base_report.clone();
    bad_authority["verdict"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-side-effect-authority",
        bad_authority,
        None,
        "verdict.route_admitted must be false",
    ));

    let mut bad_report_authority = base_report.clone();
    bad_report_authority["authority"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-side-effect-report-authority",
        bad_report_authority,
        None,
        "authority.route_admitted must be false",
    ));

    let mut stale_report_head = base_report.clone();
    stale_report_head["source"]["repo_head"] = serde_json::json!("0".repeat(40));
    cases.push((
        "stale-side-effect-head",
        stale_report_head,
        None,
        "source.repo_head",
    ));

    let mut stale_report_build = base_report.clone();
    stale_report_build["source"]["ay_build"]["commit"] = serde_json::json!("0".repeat(40));
    cases.push((
        "stale-side-effect-build",
        stale_report_build,
        None,
        "ay_build.commit",
    ));

    let mut bad_sha = base_report.clone();
    bad_sha["input"]["sha256"] = serde_json::json!("0".repeat(64));
    cases.push(("bad-side-effect-sha", bad_sha, None, "input.sha256"));

    let side_effect = dir.path().join("valid-side-effect.json");
    fs::write(
        &side_effect,
        serde_json::to_string_pretty(&base_report).expect("serialize valid side-effect report"),
    )
    .expect("write valid side-effect report");
    let side_effect_sha = sha256_hex(
        fs::read_to_string(&side_effect)
            .expect("read side-effect report")
            .as_bytes(),
    );
    let mut stale_frontier = tiny_residual_side_effect_frontier(cnf_text, &side_effect_sha);
    stale_frontier["source"]["repo_head"] = serde_json::json!("1".repeat(40));
    cases.push((
        "stale-frontier-head",
        base_report.clone(),
        Some(stale_frontier),
        "source.repo_head",
    ));

    let mut stale_frontier_upstream_build =
        tiny_residual_side_effect_frontier(cnf_text, &side_effect_sha);
    stale_frontier_upstream_build["assignment_local_search_report"]["ay_build"]["commit"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-frontier-upstream-build",
        base_report,
        Some(stale_frontier_upstream_build),
        "ay_build.commit",
    ));

    for (case, report, frontier_report, expected_stderr) in cases {
        let side_effect = dir.path().join(format!("{case}-side-effect.json"));
        fs::write(
            &side_effect,
            serde_json::to_string_pretty(&report).expect("serialize rejection side-effect report"),
        )
        .expect("write rejection side-effect report");
        let frontier = frontier_report.map(|frontier_report| {
            let path = dir.path().join(format!("{case}-frontier.json"));
            fs::write(
                &path,
                serde_json::to_string_pretty(&frontier_report)
                    .expect("serialize rejection frontier report"),
            )
            .expect("write rejection frontier report");
            path
        });

        let mut command = Command::new(ay());
        command
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "residual-side-effect-backbone",
                "--target-cnf",
            ])
            .arg(&cnf)
            .arg("--side-effect-report")
            .arg(&side_effect);
        if let Some(frontier) = &frontier {
            command.arg("--frontier-report").arg(frontier);
        }
        let output = command
            .arg("--output")
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect("spawn ay sat-comp-repair residual-side-effect-backbone rejection");

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
    }
}

fn tiny_introduced_clause_backfill_frontier_json() -> Value {
    let authority = diagnostic_authority_json();
    let frontier = serde_json::json!({
        "seen_clause_references": 3,
        "deduped_duplicate_clause_references": 1,
        "unique_clause_count": 2,
        "one_based_clause_ids": [3, 4],
        "introduced_clause_occurrences": 3,
        "unique_introduced_clause_count": 2,
        "unique_introduced_one_based_clause_ids": [3, 4],
        "frontier_clause_var_count": 4,
        "frontier_clause_one_based_vars": [2, 3, 4, 5],
        "candidate_var_count": 3,
        "candidate_one_based_vars": [1, 2, 4],
        "clauses": [
            {
                "one_based_clause_id": 3,
                "original_clause_lits": [-2, 3, 4],
                "original_clause_one_based_vars": [2, 3, 4],
                "candidate_one_based_vars": [1, 2, 4],
                "occurrence_count": 2,
                "authority": authority,
            },
            {
                "one_based_clause_id": 4,
                "original_clause_lits": [-5],
                "original_clause_one_based_vars": [5],
                "candidate_one_based_vars": [4],
                "occurrence_count": 1,
                "authority": authority,
            }
        ],
        "rows": [
            {
                "round": 1,
                "top_candidate_rank": 1,
                "introduced_one_based_clause_id": 3,
                "original_clause_lits": [-2, 3, 4],
                "original_clause_one_based_vars": [2, 3, 4],
                "candidate_one_based_set_values": [
                    { "var": 1, "value": true },
                    { "var": 2, "value": false }
                ],
                "candidate_one_based_vars": [1, 2],
                "source_frame_row_ids": ["remaining_clause_value:clause_1:lit_1:var_1"],
                "candidate_one_based_clause_ids": [1],
                "candidate_residual_falsified_clause_count": 3,
                "net_residual_delta": 2,
                "introduced_residual_count": 2,
                "affected_one_based_clause_ids": [1, 3],
                "cleared_round_start_residual_one_based_clause_ids": [1],
                "authority": authority,
            },
            {
                "round": 1,
                "top_candidate_rank": 2,
                "introduced_one_based_clause_id": 3,
                "original_clause_lits": [-2, 3, 4],
                "original_clause_one_based_vars": [2, 3, 4],
                "candidate_one_based_set_values": [
                    { "var": 2, "value": false },
                    { "var": 4, "value": true }
                ],
                "candidate_one_based_vars": [2, 4],
                "source_frame_row_ids": ["remaining_clause_value:clause_2:lit_1:var_4"],
                "candidate_one_based_clause_ids": [2],
                "candidate_residual_falsified_clause_count": 2,
                "net_residual_delta": 1,
                "introduced_residual_count": 1,
                "affected_one_based_clause_ids": [2, 3],
                "cleared_round_start_residual_one_based_clause_ids": [2],
                "authority": authority,
            },
            {
                "round": 2,
                "top_candidate_rank": 1,
                "introduced_one_based_clause_id": 4,
                "original_clause_lits": [-5],
                "original_clause_one_based_vars": [5],
                "candidate_one_based_set_values": [
                    { "var": 4, "value": true }
                ],
                "candidate_one_based_vars": [4],
                "source_frame_row_ids": ["remaining_clause_value:clause_4:lit_1:var_4"],
                "candidate_one_based_clause_ids": [4],
                "candidate_residual_falsified_clause_count": 1,
                "net_residual_delta": 0,
                "introduced_residual_count": 1,
                "affected_one_based_clause_ids": [4],
                "cleared_round_start_residual_one_based_clause_ids": [4],
                "authority": authority,
            }
        ],
    });
    serde_json::json!({
        "schema": "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
        "issue": 9424,
        "scoreboard_row": "Circuit_multiplier22",
        "source": {
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
            "note": "test fixture diagnostic-only frontier report",
        },
        "assignment_local_search_report": {
            "path": "tiny-assignment-local-search.json",
            "sha256": "1".repeat(64),
            "schema": "ay.satcomp-circuit-assignment-local-search/v1",
            "repo_head": current_git_head(),
            "ay_build": current_ay_build_json(),
        },
        "input": {
            "path": "tiny-introduced-backfill.cnf",
            "sha256": "0".repeat(64),
            "num_vars": 5,
            "num_clauses": 4,
        },
        "introduced_clauses": frontier,
        "frontier": frontier,
        "authority": authority,
        "verdict": {
            "diagnostic_only": true,
            "introduced_clause_frontier_recovered": true,
            "route_admitted": false,
            "sat_output_authority": false,
            "model_output_authority": false,
            "proof_output_authority": false,
            "solver_verdict_authority": false,
            "sat_comp_progress_claim": false,
        },
    })
}

fn tiny_introduced_clause_backfill_search_cnf() -> &'static str {
    "p cnf 5 4\n1 0\n-4 0\n-2 3 4 0\n-5 0\n"
}

fn write_tiny_introduced_clause_backfill_search_fixture(dir: &Path) -> (PathBuf, PathBuf, PathBuf) {
    let cnf = dir.join("tiny-introduced-backfill-search.cnf");
    let ledger = dir.join("w210.tsv");
    let cnf_text = tiny_introduced_clause_backfill_search_cnf();
    fs::write(&cnf, cnf_text).expect("write search target CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\ttrue\n3\tfalse\n4\tfalse\n5\ttrue\n",
    )
    .expect("write search W210 ledger");

    let mut frontier_report = tiny_introduced_clause_backfill_frontier_json();
    frontier_report["input"]["path"] = serde_json::json!(cnf.to_string_lossy());
    frontier_report["input"]["sha256"] = serde_json::json!(sha256_hex(cnf_text.as_bytes()));

    let frontier = dir.join("introduced-clause-backfill-frontier.json");
    let candidates = dir.join("introduced-clause-backfill-candidates.json");
    fs::write(
        &frontier,
        serde_json::to_string_pretty(&frontier_report).expect("serialize frontier report"),
    )
    .expect("write frontier report");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-candidates",
            "--frontier-report",
        ])
        .arg(&frontier)
        .arg("--output")
        .arg(&candidates)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-candidates");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-candidates should produce the search input; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (cnf, ledger, candidates)
}

fn tiny_introduced_clause_backfill_search_outside_radius_cnf() -> &'static str {
    "p cnf 7 6\n1 0\n-4 0\n-2 3 4 0\n-5 0\n6 -7 0\n-6 7 0\n"
}

fn write_tiny_introduced_clause_backfill_search_outside_radius_fixture(
    dir: &Path,
) -> (PathBuf, PathBuf, PathBuf) {
    let cnf = dir.join("tiny-introduced-backfill-search-outside-radius.cnf");
    let ledger = dir.join("w210.tsv");
    let cnf_text = tiny_introduced_clause_backfill_search_outside_radius_cnf();
    fs::write(&cnf, cnf_text).expect("write outside-radius search target CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\ttrue\n3\tfalse\n4\tfalse\n5\ttrue\n6\ttrue\n7\ttrue\n",
    )
    .expect("write outside-radius search W210 ledger");

    let mut frontier_report = tiny_introduced_clause_backfill_frontier_json();
    frontier_report["input"]["path"] = serde_json::json!(cnf.to_string_lossy());
    frontier_report["input"]["sha256"] = serde_json::json!(sha256_hex(cnf_text.as_bytes()));
    frontier_report["input"]["num_vars"] = serde_json::json!(7);
    frontier_report["input"]["num_clauses"] = serde_json::json!(6);

    let frontier = dir.join("introduced-clause-backfill-frontier.json");
    let candidates = dir.join("introduced-clause-backfill-candidates.json");
    fs::write(
        &frontier,
        serde_json::to_string_pretty(&frontier_report).expect("serialize frontier report"),
    )
    .expect("write frontier report");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-candidates",
            "--frontier-report",
        ])
        .arg(&frontier)
        .arg("--output")
        .arg(&candidates)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-candidates");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-candidates should produce the outside-radius search input; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (cnf, ledger, candidates)
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_candidates_writes_diagnostic_artifacts() {
    let dir = tempdir().expect("temp dir");
    let frontier = dir.path().join("introduced-clause-backfill-frontier.json");
    let out = dir
        .path()
        .join("introduced-clause-backfill-candidates.json");
    let candidate_tsv = dir.path().join("introduced-clause-backfill-candidates.tsv");
    let clause_window_tsv = dir
        .path()
        .join("introduced-clause-backfill-clause-windows.tsv");
    fs::write(
        &frontier,
        serde_json::to_string_pretty(&tiny_introduced_clause_backfill_frontier_json())
            .expect("serialize frontier report"),
    )
    .expect("write frontier report");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-candidates",
            "--frontier-report",
        ])
        .arg(&frontier)
        .arg("--output")
        .arg(&out)
        .arg("--candidate-var-tsv-output")
        .arg(&candidate_tsv)
        .arg("--clause-window-tsv-output")
        .arg(&clause_window_tsv)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-candidates");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-candidates should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read introduced-clause candidate JSON"),
    )
    .expect("parse introduced-clause candidate JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-introduced-clause-backfill-candidates/v1",
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["frontier_clause_occurrences"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["deduped_duplicate_clause_references"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["unique_introduced_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(report["counts"]["candidate_var_count"], 3, "{report:#}");
    assert_eq!(
        report["counts"]["candidate_var_occurrences"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["counts"]["candidate_clause_pair_count"], 4,
        "{report:#}"
    );
    assert_eq!(report["counts"]["clause_window_count"], 2, "{report:#}");
    assert_eq!(report["counts"]["window_var_count"], 5, "{report:#}");
    assert_eq!(
        report["candidates"]["candidate_one_based_vars"],
        serde_json::json!([1, 2, 4]),
        "{report:#}"
    );
    assert_eq!(
        report["clause_windows"]["one_based_clause_ids"],
        serde_json::json!([3, 4]),
        "{report:#}"
    );
    assert_eq!(report["authority"]["classification"], "diagnostic_only");
    assert_eq!(report["authority"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["authority"]["sat_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["model_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["proof_output_authority"], false,
        "{report:#}"
    );
    assert_diagnostic_only(&report);

    let candidate_tsv_text =
        fs::read_to_string(&candidate_tsv).expect("read backfill candidate TSV");
    let candidate_tsv_lines: Vec<_> = candidate_tsv_text.lines().collect();
    assert_eq!(
        candidate_tsv_lines,
        vec![
            "original_var\tsource_kind\tintroduced_unique_clause_count\tintroduced_clause_occurrences\tintroduced_one_based_clause_ids\tfrontier_clause_one_based_vars",
            "1\tintroduced_clause_backfill_candidate\t1\t1\t3\t2 3 4",
            "2\tintroduced_clause_backfill_candidate\t1\t2\t3\t2 3 4",
            "4\tintroduced_clause_backfill_candidate\t2\t2\t3 4\t2 3 4 5",
        ],
        "candidate TSV should be assignment-local-search --candidate-file compatible and aggregate duplicate clause rows by candidate var:\n{candidate_tsv_text}"
    );

    let clause_window_tsv_text =
        fs::read_to_string(&clause_window_tsv).expect("read backfill clause-window TSV");
    let clause_window_tsv_lines: Vec<_> = clause_window_tsv_text.lines().collect();
    assert_eq!(
        clause_window_tsv_lines,
        vec![
            "one_based_clause_id\toriginal_clause_lits\tclause_one_based_vars\tcandidate_one_based_vars\twindow_one_based_vars\toccurrence_count",
            "3\t-2 3 4\t2 3 4\t1 2 4\t1 2 3 4\t2",
            "4\t-5\t5\t4\t4 5\t1",
        ],
        "clause-window TSV should emit one deduped row per introduced clause:\n{clause_window_tsv_text}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_candidates_rejects_untrusted_frontiers() {
    let dir = tempdir().expect("temp dir");
    let out = dir
        .path()
        .join("introduced-clause-backfill-candidates.json");
    let base_report = tiny_introduced_clause_backfill_frontier_json();

    let mut cases = Vec::new();

    let mut bad_authority = base_report.clone();
    bad_authority["authority"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-frontier-authority",
        bad_authority,
        "authority.route_admitted must be false",
    ));

    let mut stale_head = base_report.clone();
    stale_head["source"]["repo_head"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-frontier-head", stale_head, "source.repo_head"));

    let mut stale_build = base_report.clone();
    stale_build["source"]["ay_build"]["commit"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-frontier-build", stale_build, "ay_build.commit"));

    let mut stale_upstream_head = base_report.clone();
    stale_upstream_head["assignment_local_search_report"]["repo_head"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-frontier-upstream-head",
        stale_upstream_head,
        "assignment_local_search_report.repo_head",
    ));

    let mut stale_upstream_build = base_report.clone();
    stale_upstream_build["assignment_local_search_report"]["ay_build"]["commit"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-frontier-upstream-build",
        stale_upstream_build,
        "ay_build.commit",
    ));

    let mut bad_schema = base_report;
    bad_schema["schema"] =
        serde_json::json!("ay.satcomp-circuit-introduced-clause-backfill-frontier/v0");
    cases.push((
        "bad-frontier-schema",
        bad_schema,
        "ay.satcomp-circuit-introduced-clause-backfill-frontier/v1",
    ));

    for (case, report, expected_stderr) in cases {
        let frontier = dir.path().join(format!("{case}.json"));
        fs::write(
            &frontier,
            serde_json::to_string_pretty(&report).expect("serialize bad frontier report"),
        )
        .expect("write bad frontier report");

        let output = Command::new(ay())
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "introduced-clause-backfill-candidates",
                "--frontier-report",
            ])
            .arg(&frontier)
            .arg("--output")
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect("spawn ay sat-comp-repair introduced-clause-backfill-candidates rejection");

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_writes_diagnostic_report() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, candidates) =
        write_tiny_introduced_clause_backfill_search_fixture(dir.path());
    let out = dir.path().join("introduced-clause-backfill-search.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--candidates-report")
        .arg(&candidates)
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-search");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read introduced-clause backfill search JSON"),
    )
    .expect("parse introduced-clause backfill search JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-introduced-clause-backfill-search/v1",
        "{report:#}"
    );
    assert_eq!(
        report["introduced_clause_backfill_candidates_report"]["schema"],
        "ay.satcomp-circuit-introduced-clause-backfill-candidates/v1",
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["source_candidate_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_source_candidate_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["window_var_count"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_candidate_count"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["introduced_clause_count"], 2,
        "{report:#}"
    );
    assert_eq!(report["search"]["candidate_count"], 5, "{report:#}");
    assert_eq!(report["authority"]["classification"], "diagnostic_only");
    assert_eq!(report["authority"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["authority"]["sat_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["model_output_authority"], false,
        "{report:#}"
    );
    assert_eq!(
        report["authority"]["proof_output_authority"], false,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_applies_seed_set_file_diagnostic_only() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, candidates) =
        write_tiny_introduced_clause_backfill_search_fixture(dir.path());
    let seed = dir.path().join("introduced-backfill-seed.tsv");
    let out = dir
        .path()
        .join("introduced-clause-backfill-search-seeded.json");

    fs::write(&seed, "original_var\tcandidate_value\n1\ttrue\n5\tfalse\n")
        .expect("write introduced backfill seed set");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--candidates-report")
        .arg(&candidates)
        .arg("--seed-set-file")
        .arg(&seed)
        .args(["--pair-rounds", "0", "--output"])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair seeded introduced-clause-backfill-search");

    assert!(
        output.status.success(),
        "seeded introduced-clause-backfill-search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read seeded introduced-clause backfill search JSON"),
    )
    .expect("parse seeded introduced-clause backfill search JSON");
    assert_eq!(report["seed"]["enabled"], true, "{report:#}");
    assert_eq!(report["seed"]["set_var_count"], 2, "{report:#}");
    assert_eq!(
        report["seed"]["one_based_set_values"],
        serde_json::json!([{ "var": 1, "value": true }, { "var": 5, "value": false }]),
        "{report:#}"
    );
    assert_eq!(
        report["seed"]["changed_from_w210_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["seed"]["residual_falsified_one_based_clause_ids"],
        serde_json::json!([3]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["rounds"][0]["starting_residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["rounds"][0]["selected_one_based_var"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["original_dimacs_valid_model"], true,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["one_based_set_values"],
        serde_json::json!([
            { "var": 1, "value": true },
            { "var": 2, "value": false },
            { "var": 5, "value": false }
        ]),
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_rejects_conflicting_seed_set_files() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, candidates) =
        write_tiny_introduced_clause_backfill_search_fixture(dir.path());
    let seed_a = dir.path().join("seed-a.tsv");
    let seed_b = dir.path().join("seed-b.tsv");
    let out = dir
        .path()
        .join("introduced-clause-backfill-search-conflicting-seed.json");

    fs::write(&seed_a, "original_var\tcandidate_value\n1\ttrue\n")
        .expect("write first introduced backfill seed set");
    fs::write(&seed_b, "original_var\tcandidate_value\n1\tfalse\n")
        .expect("write second introduced backfill seed set");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--candidates-report")
        .arg(&candidates)
        .arg("--seed-set-file")
        .arg(&seed_a)
        .arg("--seed-set-file")
        .arg(&seed_b)
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair conflicting seeded introduced-clause-backfill-search");

    assert!(
        !output.status.success(),
        "conflicting seeded introduced-clause-backfill-search should fail; stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("conflicting set values for variable 1"),
        "stderr should explain conflicting seed set values:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !out.exists(),
        "conflicting seed files must not write a diagnostic report with authority fields"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_include_outside_radius_vars_materializes_extra_diagnostic_only(
) {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, candidates) =
        write_tiny_introduced_clause_backfill_search_outside_radius_fixture(dir.path());
    let out = dir
        .path()
        .join("introduced-clause-backfill-search-outside-radius.json");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "introduced-clause-backfill-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--candidates-report")
        .arg(&candidates)
        .args([
            "--outside-radius",
            "0",
            "--include-outside-radius-vars",
            "--outside-radius-var-limit",
            "2",
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair introduced-clause-backfill-search outside-radius");

    assert!(
        output.status.success(),
        "introduced-clause-backfill-search outside-radius materialization should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out)
            .expect("read introduced-clause backfill outside-radius search JSON"),
    )
    .expect("parse introduced-clause backfill outside-radius search JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-introduced-clause-backfill-search/v1",
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["include_outside_radius_vars"], true,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_var_limit"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["source_candidate_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_source_candidate_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["window_var_count"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_window_only_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_w210_residual_one_based_clause_ids"],
        serde_json::json!([1, 3, 4]),
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["one_based_outside_radius_vars"],
        serde_json::json!([6, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_only_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["one_based_outside_radius_only_vars"],
        serde_json::json!([6, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_free_var_count"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_window_overlap_var_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_window_overlap_one_based_vars"],
        serde_json::json!([]),
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_outside_radius_only_var_count"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["outside_radius_vars_truncated"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_outside_radius_only_one_based_vars"],
        serde_json::json!([6, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_candidate_count"], 7,
        "{report:#}"
    );
    assert_eq!(
        report["materialized_candidates"]["selected_candidate_one_based_vars"],
        serde_json::json!([1, 2, 4, 3, 5, 6, 7]),
        "{report:#}"
    );
    assert_eq!(report["search"]["candidate_count"], 7, "{report:#}");
    assert_eq!(report["authority"]["classification"], "diagnostic_only");
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_include_outside_radius_vars_validates_options()
{
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, candidates) =
        write_tiny_introduced_clause_backfill_search_outside_radius_fixture(dir.path());

    let cases: Vec<(&str, Vec<&str>, &str)> = vec![
        (
            "zero-outside-radius-limit",
            vec!["--outside-radius", "0", "--outside-radius-var-limit", "0"],
            "--outside-radius-var-limit",
        ),
        (
            "invalid-radius",
            vec![
                "--outside-radius",
                "not-a-radius",
                "--outside-radius-var-limit",
                "2",
            ],
            "--outside-radius",
        ),
    ];

    for (case, extra_args, expected_stderr) in cases {
        let out = dir
            .path()
            .join(format!("introduced-clause-backfill-search-{case}.json"));
        let output = Command::new(ay())
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "introduced-clause-backfill-search",
                "--target-cnf",
            ])
            .arg(&cnf)
            .arg("--w210-ledger")
            .arg(&ledger)
            .arg("--candidates-report")
            .arg(&candidates)
            .arg("--include-outside-radius-vars")
            .args(extra_args)
            .args(["--rounds", "0", "--pair-rounds", "0", "--output"])
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect(
                "spawn ay sat-comp-repair introduced-clause-backfill-search outside-radius rejection",
            );

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_introduced_clause_backfill_search_rejects_untrusted_candidate_reports() {
    let dir = tempdir().expect("temp dir");
    let (cnf, ledger, base_report_path) =
        write_tiny_introduced_clause_backfill_search_fixture(dir.path());
    let base_report: Value = serde_json::from_str(
        &fs::read_to_string(&base_report_path).expect("read base candidate report"),
    )
    .expect("parse base candidate report");

    let mut cases = Vec::new();

    let mut bad_schema = base_report.clone();
    bad_schema["schema"] =
        serde_json::json!("ay.satcomp-circuit-introduced-clause-backfill-candidates/v0");
    cases.push((
        "bad-candidate-schema",
        bad_schema,
        "ay.satcomp-circuit-introduced-clause-backfill-candidates/v1",
    ));

    let mut bad_authority = base_report.clone();
    bad_authority["authority"]["route_admitted"] = serde_json::json!(true);
    cases.push((
        "bad-candidate-authority",
        bad_authority,
        "authority.route_admitted must be false",
    ));

    let mut stale_head = base_report.clone();
    stale_head["source"]["repo_head"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-candidate-head", stale_head, "source.repo_head"));

    let mut stale_build = base_report.clone();
    stale_build["source"]["ay_build"]["commit"] = serde_json::json!("0".repeat(40));
    cases.push(("stale-candidate-build", stale_build, "ay_build.commit"));

    let mut stale_embedded_frontier_head = base_report.clone();
    stale_embedded_frontier_head["introduced_clause_backfill_frontier"]["repo_head"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-embedded-frontier-head",
        stale_embedded_frontier_head,
        "introduced_clause_backfill_frontier.repo_head",
    ));

    let mut stale_embedded_frontier_build = base_report.clone();
    stale_embedded_frontier_build["introduced_clause_backfill_frontier"]["ay_build"]["commit"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-embedded-frontier-build",
        stale_embedded_frontier_build,
        "introduced_clause_backfill_frontier.ay_build.commit",
    ));

    let mut stale_embedded_upstream_head = base_report.clone();
    stale_embedded_upstream_head["introduced_clause_backfill_frontier"]
        ["assignment_local_search_report"]["repo_head"] = serde_json::json!("0".repeat(40));
    cases.push((
        "stale-embedded-upstream-head",
        stale_embedded_upstream_head,
        "assignment_local_search_report.repo_head",
    ));

    let mut stale_embedded_upstream_build = base_report.clone();
    stale_embedded_upstream_build["introduced_clause_backfill_frontier"]
        ["assignment_local_search_report"]["ay_build"]["commit"] =
        serde_json::json!("0".repeat(40));
    cases.push((
        "stale-embedded-upstream-build",
        stale_embedded_upstream_build,
        "ay_build.commit",
    ));

    let mut bad_candidate_source = base_report.clone();
    bad_candidate_source["candidates"]["source"] =
        serde_json::json!("introduced_clauses.clauses[].original_clause_one_based_vars");
    cases.push((
        "bad-candidate-source",
        bad_candidate_source,
        "candidates.source",
    ));

    let mut bad_verdict_source = base_report.clone();
    bad_verdict_source["verdict"]["candidate_vars_source"] =
        serde_json::json!("introduced_clauses.clauses[].original_clause_one_based_vars");
    cases.push((
        "bad-verdict-candidate-source",
        bad_verdict_source,
        "candidate_vars_source",
    ));

    let mut bad_verdict_authority = base_report;
    bad_verdict_authority["verdict"]["sat_comp_progress_claim"] = serde_json::json!(true);
    cases.push((
        "bad-candidate-verdict-authority",
        bad_verdict_authority,
        "verdict.sat_comp_progress_claim must be false",
    ));

    for (case, report, expected_stderr) in cases {
        let candidates = dir.path().join(format!("{case}.json"));
        let out = dir.path().join(format!("{case}-search.json"));
        fs::write(
            &candidates,
            serde_json::to_string_pretty(&report).expect("serialize bad candidate report"),
        )
        .expect("write bad candidate report");

        let output = Command::new(ay())
            .current_dir(repo_root())
            .args([
                "submission",
                "preflight",
                "sat-comp-repair",
                "introduced-clause-backfill-search",
                "--target-cnf",
            ])
            .arg(&cnf)
            .arg("--w210-ledger")
            .arg(&ledger)
            .arg("--candidates-report")
            .arg(&candidates)
            .arg("--output")
            .arg(&out)
            .output_timeout(Duration::from_secs(55))
            .expect("spawn ay sat-comp-repair introduced-clause-backfill-search rejection");

        assert!(
            !output.status.success(),
            "{case} should fail closed; code={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected_stderr),
            "{case} stderr should contain {expected_stderr:?}; stderr:\n{stderr}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_side_effect_prune_keeps_non_worsening_and_top_per_clause(
) {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-source-frame-choice-side-effect-prune.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let remaining = dir.path().join("remaining-clause-value-ledger.tsv");
    let out = dir
        .path()
        .join("source-frame-choice-side-effect-prune.json");

    fs::write(
        &cnf,
        "p cnf 8 16\n1 2 3 4 0\n5 6 7 8 0\n-1 0\n-2 0\n-3 0\n-3 0\n-4 0\n-4 0\n-4 0\n-5 0\n-6 0\n-7 0\n-7 0\n-8 0\n-8 0\n-8 0\n",
    )
    .expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n4\tfalse\n5\tfalse\n6\tfalse\n7\tfalse\n8\tfalse\n",
    )
    .expect("write ledger");
    fs::write(
        &source_rows,
        "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
    )
    .expect("write empty source frame rows");
    fs::write(
        &remaining,
        concat!(
            "clause_index_1_based\tclassification\tvariables\tsource_counts\tfrontier_vars\tcyclic_scc_vars\tforced_gate_vars\tactive_in_cegar_best\tall_literals_false_under_best_assignment\tliteral_values\tclause\n",
            "1\ttest\t1 2 3 4\t{}\t1 2 3 4\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":1,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":1,\"\"var_value\"\":false},{\"\"lit\"\":2,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":2,\"\"var_value\"\":false},{\"\"lit\"\":3,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":3,\"\"var_value\"\":false},{\"\"lit\"\":4,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":4,\"\"var_value\"\":false}]\"\t1 2 3 4\n",
            "2\ttest\t5 6 7 8\t{}\t5 6 7 8\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":5,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":5,\"\"var_value\"\":false},{\"\"lit\"\":6,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":6,\"\"var_value\"\":false},{\"\"lit\"\":7,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":7,\"\"var_value\"\":false},{\"\"lit\"\":8,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":8,\"\"var_value\"\":false}]\"\t5 6 7 8\n",
        ),
    )
    .expect("write remaining clause ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--source-frame-choice-current-remaining-clause-value-ledger")
        .arg(&remaining)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-side-effect-top-per-clause",
            "1",
            "--source-frame-choice-beam-width",
            "32",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search side-effect prune mode");

    assert!(
        output.status.success(),
        "side-effect prune local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read side-effect prune JSON"))
            .expect("parse side-effect prune JSON");
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 8,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_selected_rows"], 6,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_input_rows"], 8,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_kept_rows"], 6,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_non_worsening_rows"], 4,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_top_per_clause_rows"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_pruned_rows"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_pruning_authority"], "diagnostic_only",
        "{report:#}"
    );
    let top_candidates =
        report["search"]["source_frame_choice_rounds"][0]["top_candidates"].to_string();
    for kept_var in ["var_1", "var_2", "var_3", "var_5", "var_6", "var_7"] {
        assert!(
            top_candidates.contains(kept_var),
            "top candidates should include {kept_var}: {report:#}"
        );
    }
    assert!(
        !top_candidates.contains("var_4"),
        "worse clause-1 side-effect choice should be pruned: {report:#}"
    );
    assert!(
        !top_candidates.contains("var_8"),
        "worse clause-2 side-effect choice should be pruned: {report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 0,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_side_effect_prune_allows_zero_top_per_clause(
) {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame-choice-prune-zero.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let out = dir.path().join("source-frame-choice-prune-zero.json");

    fs::write(&cnf, "p cnf 1 1\n1 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        concat!(
            "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
            "r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\tfalse\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n",
        ),
    )
    .expect("write source frame rows");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "1",
            "--source-frame-choice-side-effect-top-per-clause",
            "0",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search zero prune mode");

    assert!(
        output.status.success(),
        "zero top-per-clause should keep only non-worsening rows; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read zero-prune JSON"))
            .expect("parse zero-prune JSON");
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_input_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_non_worsening_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_side_effect_prune_top_per_clause_rows"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_selected_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_source_frame_choice_reports_remaining_clause_parse_errors(
) {
    let dir = tempdir().expect("temp dir");
    let cnf = dir
        .path()
        .join("tiny-source-frame-choice-remaining-ledger-bad-json.cnf");
    let ledger = dir.path().join("w210.tsv");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let remaining = dir.path().join("remaining-clause-value-ledger.tsv");
    let out = dir
        .path()
        .join("source-frame-choice-remaining-ledger-bad-json.json");

    fs::write(&cnf, "p cnf 2 2\n1 0\n2 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\tfalse\n2\tfalse\n").expect("write ledger");
    fs::write(
        &source_rows,
        "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n",
    )
    .expect("write empty source frame rows");
    fs::write(
        &remaining,
        concat!(
            "clause_index_1_based\tclassification\tvariables\tsource_counts\tfrontier_vars\tcyclic_scc_vars\tforced_gate_vars\tactive_in_cegar_best\tall_literals_false_under_best_assignment\tliteral_values\tclause\n",
            "1\ttest\t1\t{}\t1\t.\t.\tfalse\ttrue\tnot-json\t1\n",
            "2\ttest\t2\t{}\t2\t.\t.\tfalse\ttrue\t\"[{\"\"lit\"\":2,\"\"literal_value\"\":false,\"\"source\"\":\"\"frontier_choice_cegar\"\",\"\"var\"\":2,\"\"var_value\"\":false}]\"\t2\n",
        ),
    )
    .expect("write remaining clause ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--source-frame-choice-current-remaining-clause-value-ledger")
        .arg(&remaining)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--source-frame-choice-rounds",
            "1",
            "--source-frame-choice-limit",
            "8",
            "--source-frame-choice-beam-width",
            "8",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search malformed ledger choice mode");

    assert!(
        output.status.success(),
        "malformed remaining-clause choice local search should report and continue; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_str(
        &fs::read_to_string(&out).expect("read malformed remaining-clause choice JSON"),
    )
    .expect("parse malformed remaining-clause choice JSON");
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_rows_seen"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_parse_errors"], 1,
        "{report:#}"
    );
    assert!(
        report["search"]["source_frame_choice_remaining_clause_parse_error_samples"][0]
            .as_str()
            .expect("parse error sample")
            .contains("literal_values"),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_remaining_clause_choice_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["source_frame_choice_candidate_rows"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_diagnostic_only(&report);
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_counts_group_breaks() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-group-break.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("group-break.json");

    fs::write(&cnf, "p cnf 3 2\n1 2 3 0\n-1 -2 -3 0\n").expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--group-rounds",
            "1",
            "--group-size",
            "3",
            "--group-window-size",
            "3",
            "--candidate-vars",
            "1,2,3",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search group break mode");

    assert!(
        output.status.success(),
        "group break local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read group break JSON"))
            .expect("parse group break JSON");
    assert_eq!(
        report["search"]["group_scoring"], "incremental_affected_clause_delta",
        "{report:#}"
    );
    assert_eq!(
        report["search"]["evaluated_group_affected_clauses"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["improved"], false,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["selected_one_based_vars"],
        Value::Null,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["top_candidates"][0]["residual_falsified_clause_count"],
        1,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["top_candidates"][0]
            ["residual_falsified_one_based_clause_ids"],
        serde_json::json!([2]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 0,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_counts_group_delta_with_carried_residual() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-group-delta.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("group-delta.json");

    fs::write(
        &cnf,
        "p cnf 4 7\n1 2 3 0\n1 2 0\n2 3 0\n1 3 0\n-1 -2 -3 0\n-1 -2 0\n4 0\n",
    )
    .expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--group-rounds",
            "1",
            "--group-size",
            "3",
            "--group-window-size",
            "3",
            "--candidate-vars",
            "1,2,3",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search group delta mode");

    assert!(
        output.status.success(),
        "group delta local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read group delta JSON"))
            .expect("parse group delta JSON");
    assert_eq!(
        report["baseline_w210"]["residual_falsified_clause_count"], 5,
        "{report:#}"
    );
    assert_eq!(
        report["baseline_w210"]["residual_falsified_one_based_clause_ids"],
        serde_json::json!([1, 2, 3, 4, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["evaluated_group_affected_clauses"], 6,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["selected_one_based_vars"],
        serde_json::json!([1, 2, 3]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["selected_new_values"],
        serde_json::json!([true, true, true]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["ending_residual_falsified_clause_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_rounds"][0]["top_candidates"][0]
            ["residual_falsified_one_based_clause_ids"],
        serde_json::json!([5, 6, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_one_based_clause_ids"],
        serde_json::json!([5, 6, 7]),
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 3,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["original_dimacs_valid_model"], false,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_assignment_local_search_filters_group_required_vars() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-group-required.cnf");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("group-required.json");

    fs::write(
        &cnf,
        "p cnf 4 7\n1 2 3 0\n-1 2 3 0\n1 -2 3 0\n1 2 -3 0\n-1 -2 3 0\n-1 2 -3 0\n1 -2 -3 0\n",
    )
    .expect("write CNF");
    fs::write(
        &ledger,
        "original_var\tvalue\n1\tfalse\n2\tfalse\n3\tfalse\n4\tfalse\n",
    )
    .expect("write ledger");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "assignment-local-search",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--w210-ledger")
        .arg(&ledger)
        .args([
            "--rounds",
            "0",
            "--pair-rounds",
            "0",
            "--group-rounds",
            "1",
            "--group-size",
            "3",
            "--group-window-size",
            "4",
            "--candidate-vars",
            "1,2,3,4",
            "--group-require-vars",
            "4",
            "--output",
        ])
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair assignment-local-search required group mode");

    assert!(
        output.status.success(),
        "required group local search should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read required group JSON"))
            .expect("parse required group JSON");
    assert_eq!(
        report["search"]["group_required_one_based_vars"],
        serde_json::json!([4]),
        "{report:#}"
    );
    assert_eq!(
        report["search"]["group_required_min_count"], 1,
        "{report:#}"
    );
    assert_eq!(report["search"]["group_template_count"], 3, "{report:#}");
    assert_eq!(report["search"]["evaluated_group_flips"], 3, "{report:#}");
    assert_eq!(
        report["search"]["group_rounds"][0]["selected_one_based_vars"],
        Value::Null,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["best"]["changed_from_w210_var_count"], 0,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_source_frame_audit_checks_original_clause_bindings() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-source-frame.cnf");
    let source_rows = dir.path().join("source-frame-input-rows.tsv");
    let missing_rows = dir.path().join("diagnostic-missing-source-rows.tsv");
    let hook_targets = dir.path().join("residual-clause-source-hook-targets.tsv");
    let component_hooks = dir.path().join("component-source-hook-targets.tsv");
    let ledger = dir.path().join("w210.tsv");
    let out = dir.path().join("source-frame-audit.json");

    fs::write(&cnf, "p cnf 3 2\n1 -2 0\n-1 3 0\n").expect("write CNF");
    fs::write(&ledger, "original_var\tvalue\n1\ttrue\n2\ttrue\n3\tfalse\n")
        .expect("write W210 ledger");
    let row_header = "source_frame_row_id\tclause_id\tliteral_index\tlit\tvar\tsource_family\tsource_kind\tgate_type\tsource_value\trequired_value_to_satisfy_literal\tsource_ledger_row_ids\tproduction_hook\tsource_row_status\tconstruction_action\tnegative_gate\n";
    fs::write(
        &source_rows,
        format!(
            "{row_header}r1\t1\t1\t1\t1\tw210_frontier\tfrontier\tfrontier\ttrue\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\nr2\t2\t2\t3\t3\tforced_gate_replay_bridge\tbridge\tand_gate_replay\ttrue\ttrue\t.\ttest\tinput_source_row_id_present\tkeep\tguard\n"
        ),
    )
    .expect("write source rows");
    fs::write(
        &missing_rows,
        format!(
            "{row_header}m1\t1\t2\t-2\t2\tmissing_source_row\t.\t.\t.\tfalse\t.\t.\tdiagnostic_missing_source_row\tfail closed\tguard\n"
        ),
    )
    .expect("write missing rows");
    fs::write(
        &hook_targets,
        "clause_id\tcomponent_id\twidth\tclause\tvars\tsource_frame_class\tcovered_by_required_family\tcovered_real_source_families\tall_input_source_families\trequired_literal_rows\tdiagnostic_missing_literal_rows\tgate_type_families\tresidual_cluster\tbridge_conflict_vars\tconstruction_action\tnegative_gate\n1\t1\t2\t1 -2\t1 2\tmixed\ttrue\tw210_frontier\tw210_frontier missing_source_row\t2\t1\tfrontier\tcluster\t.\tcheck\tguard\n",
    )
    .expect("write hook targets");
    fs::write(
        &component_hooks,
        "component_id\tclause_ids\tcovered_real_source_families\tdiagnostic_missing_literal_rows\n1\t1\tw210_frontier\t1\n",
    )
    .expect("write component hooks");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "source-frame-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--source-frame-rows")
        .arg(&source_rows)
        .arg("--missing-source-rows")
        .arg(&missing_rows)
        .arg("--residual-hook-targets")
        .arg(&hook_targets)
        .arg("--component-hook-targets")
        .arg(&component_hooks)
        .arg("--w210-ledger")
        .arg(&ledger)
        .arg("--w210-overlay")
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair source-frame-audit");

    assert!(
        output.status.success(),
        "source-frame-audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read source frame audit JSON"))
            .expect("parse source frame audit JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-source-frame-audit/v1",
        "{report:#}"
    );
    assert_eq!(
        report["source_frame_rows"]["audit"]["rows_accepted"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["source_frame_rows"]["audit"]["source_value_satisfies_literal"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["source_frame_rows"]["audit"]["source_value_falsifies_literal"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["diagnostic_missing_source_rows"]["audit"]["unsupported_family"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["residual_hook_targets"]["required_literal_rows"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["residual_hook_targets"]["one_based_clause_ids"],
        serde_json::json!([1]),
        "{report:#}"
    );
    assert_eq!(
        report["component_hook_targets"]["component_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["direct_assignment_from_source_rows"]["assignment_complete"], false,
        "{report:#}"
    );
    assert_eq!(
        report["w210_overlay_assignment"]["base"]["residual_falsified_clause_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["w210_overlay_assignment"]["overlay"]["changed_var_count"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["w210_overlay_assignment"]["overlay"]["residual_falsified_clause_count"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["verdict"]["w210_overlay_original_dimacs_valid_model_found"], true,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}

#[test]
#[timeout(60_000)]
fn sat_comp_repair_witness_audit_reports_gate_replay_obligations() {
    let dir = tempdir().expect("temp dir");
    let cnf = dir.path().join("tiny-and.cnf");
    let out = dir.path().join("witness-audit.json");

    fs::write(&cnf, "p cnf 3 3\n-3 1 0\n-3 2 0\n3 -1 -2 0\n").expect("write CNF");

    let output = Command::new(ay())
        .current_dir(repo_root())
        .args([
            "submission",
            "preflight",
            "sat-comp-repair",
            "witness-audit",
            "--target-cnf",
        ])
        .arg(&cnf)
        .arg("--output")
        .arg(&out)
        .output_timeout(Duration::from_secs(55))
        .expect("spawn ay sat-comp-repair witness-audit");

    assert!(
        output.status.success(),
        "witness-audit should succeed; code={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_str(&fs::read_to_string(&out).expect("read witness audit JSON"))
            .expect("parse witness audit JSON");
    assert_eq!(
        report["schema"], "ay.satcomp-circuit-witness-audit/v1",
        "{report:#}"
    );
    assert_eq!(report["gate_counts"]["and"], 1, "{report:#}");
    assert_eq!(
        report["exact_clause_validation"]["validated_total"], 1,
        "{report:#}"
    );
    assert_eq!(report["reconstruction"]["frontier_vars"], 2, "{report:#}");
    assert_eq!(
        report["reconstruction"]["derivable_gate_output_vars"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["reconstruction"]["blocked_gate_output_vars"], 0,
        "{report:#}"
    );
    assert_eq!(
        report["materialization_plan"]["direct_frontier_vars"], 2,
        "{report:#}"
    );
    assert_eq!(
        report["materialization_plan"]["acyclic_replay_order_len"], 1,
        "{report:#}"
    );
    assert_eq!(
        report["materialization_plan"]["blocked_by_cycle_output_vars"], 0,
        "{report:#}"
    );
    assert_eq!(report["verdict"]["route_admitted"], false, "{report:#}");
    assert_eq!(
        report["verdict"]["sat_comp_progress_claim"], false,
        "{report:#}"
    );
}
