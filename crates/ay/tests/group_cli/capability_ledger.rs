// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end capability-ledger provenance on DIMACS proof and env routes.

use ntest::timeout;
use std::process::Command;
use tempfile::tempdir;

const UNSAT_CNF: &str = "p cnf 1 2\n1 0\n-1 0\n";
const TWO_VAR_UNSAT_CNF: &str = "p cnf 2 3\n1 2 0\n-1 0\n-2 0\n";

fn ay_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    for name in [
        "AY_SAT_VARIANT",
        "AY_INTERNAL_SATCOMP_WRAPPER",
        "AY_SAT_PROFILE_ID",
        "AY_SAT_COMPETITION_PROFILE",
        "AY_SAT_TRACK",
        "AY_SAT_AI_CLASS",
        "AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT",
    ] {
        command.env_remove(name);
    }
    command
}

fn capability_lines(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.starts_with("c startup_capability:"))
        .collect()
}

fn capability_line<'a>(stderr: &'a str, capability: &str) -> &'a str {
    capability_lines(stderr)
        .into_iter()
        .find(|line| line.split_whitespace().nth(2) == Some(capability))
        .unwrap_or_else(|| panic!("missing startup capability {capability}; {stderr}"))
}

fn stats_json(stderr: &str) -> serde_json::Value {
    stderr
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .find(|value| value.get("mode").is_some())
        .unwrap_or_else(|| panic!("missing stats JSON object; {stderr}"))
}

#[test]
#[timeout(30_000)]
fn stats_json_contains_startup_state_and_source_without_human_rows() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .args(["--stats-json", "--no-proof", "--sat-variant", "minimal"])
        .arg(&input)
        .output()
        .expect("run JSON stats route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(!stderr.contains("c startup_capability:"), "{stderr}");
    let json = stats_json(&stderr);
    assert_eq!(json["sat.capability_plan.available"], 1);
    assert_eq!(json["sat.capability_plan.status"], "available");
    assert_eq!(json["sat.capability.preprocess.state"], "off");
    assert_eq!(json["sat.capability.preprocess.source"], 0);
    assert_eq!(json["sat.capability.preprocess.source_label"], "cli");
}

#[test]
#[timeout(30_000)]
fn stats_proof_route_emits_complete_cli_sourced_ledger() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.drat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .args(["--stats", "--sat-variant", "minimal", "--proof"])
        .arg(&proof)
        .arg(&input)
        .env_remove("AY_SAT_VARIANT")
        .output()
        .expect("run ay proof route");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected UNSAT proof run; stderr={stderr}"
    );
    let lines = capability_lines(&stderr);
    assert_eq!(lines.len(), 23, "expected every capability; {stderr}");
    assert!(
        lines
            .iter()
            .any(|line| line.contains("preprocess") && line.contains("cli")),
        "explicit --sat-variant provenance is missing; {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn stats_env_variant_names_exact_compatibility_shim() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .arg("--stats")
        .arg(&input)
        .env("AY_SAT_VARIANT", "minimal")
        .output()
        .expect("run ay env-variant route");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(
        capability_lines(&stderr)
            .iter()
            .any(|line| { line.contains("preprocess") && line.contains("env:AY_SAT_VARIANT") }),
        "environment fallback must identify its exact shim; {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn stats_cli_disables_override_startup_state_and_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .args(["--stats", "--disable", "vivify,inprocess"])
        .arg(&input)
        .env_remove("AY_SAT_VARIANT")
        .output()
        .expect("run ay with CLI disables");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    for capability in ["vivify", "probe", "backbone", "reorder"] {
        let line = capability_line(&stderr, capability);
        assert!(line.contains("off") && line.contains("cli"), "{line}");
    }
}

#[test]
#[timeout(30_000)]
fn stats_feature_env_shims_name_only_decisive_sources() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .arg("--stats")
        .arg(&input)
        .env_remove("AY_SAT_VARIANT")
        .arg("--sat-no-subst-auto")
        .arg("--sat-no-bve-sparse")
        .output()
        .expect("run ay with feature env shims");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(
        capability_line(&stderr, "congruence").contains("cli"),
        "{stderr}"
    );
    assert!(capability_line(&stderr, "bve").contains("cli"), "{stderr}");
}

#[test]
#[timeout(30_000)]
fn stats_drat_substitution_clamp_names_exact_env_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.drat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .arg(&input)
        .env_remove("AY_SAT_VARIANT")
        .arg("--sat-no-drat-subst")
        .output()
        .expect("run ay with DRAT substitution clamp");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(
        capability_line(&stderr, "decompose").contains("cli"),
        "{stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn substitution_kill_switch_is_decisive_and_cli_sourced() {
    // B36: the force-enable shims are gone; the substitution kill is the one
    // operator influence on these gates, and its provenance is cli.
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--sat-variant", "default", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-subst-auto")
        .output()
        .expect("run substitution kill");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    for capability in ["congruence", "decompose"] {
        let line = capability_line(&stderr, capability);
        assert!(line.contains("off") && line.contains("cli"), "{line}");
    }
}

#[test]
#[timeout(30_000)]
fn bve_density_threshold_is_named_only_when_it_changes_admission() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, TWO_VAR_UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .arg("--stats")
        .arg(&input)
        .args(["--sat-bve-sparse-max-density", "1"])
        .output()
        .expect("run changed BVE density threshold");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "bve");
    assert!(line.contains("off") && line.contains("cli"), "{line}");
}

#[test]
#[timeout(30_000)]
fn lrat_policy_clamps_substitution_features() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.lrat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "lrat"])
        .arg(&input)
        .output()
        .expect("run LRAT proof clamp");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    for capability in ["congruence", "decompose"] {
        // Off under LRAT whichever layer resolves it first (the proof-policy
        // clamp on instances that armed the AUTO path; the resolved profile
        // default on ones that never did).
        let line = capability_line(&stderr, capability);
        assert!(line.contains("off"), "{line}");
    }
}

#[test]
#[timeout(30_000)]
fn proof_policy_attributes_redundant_substitution_env_kills_truthfully() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");

    for (format, drat_kill) in [("lrat", false), ("drat", true)] {
        let proof = scratch.path().join(format!("proof.{format}"));
        let mut command = ay_command();
        command
            .args(["--stats", "--proof"])
            .arg(&proof)
            .args(["--proof-format", format])
            .arg(&input)
            .arg("--sat-no-subst-auto");
        if drat_kill {
            command.arg("--sat-no-drat-subst");
        }
        let output = command.output().expect("run overlapping proof/env policy");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
        for capability in ["congruence", "decompose"] {
            let line = capability_line(&stderr, capability);
            assert!(line.contains("off"), "{line}");
            if drat_kill {
                assert!(line.contains("cli"), "{line}");
            } else {
                assert!(line.contains("auto"), "{line}");
                assert!(!line.contains("env:"), "{line}");
            }
        }
    }
}

#[test]
#[timeout(30_000)]
fn probe_drat_clamp_ignores_default_only_substitution_env() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    for subst_kill in [false, true] {
        let proof = scratch.path().join(format!("probe-{subst_kill}.drat"));
        let mut command = ay_command();
        command
            .args(["--stats", "--sat-variant", "probe", "--proof"])
            .arg(&proof)
            .arg(&input)
            .arg("--sat-no-drat-subst");
        if subst_kill {
            command.arg("--sat-no-subst-auto");
        }
        let output = command.output().expect("run Probe DRAT clamp");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
        let line = capability_line(&stderr, "decompose");
        assert!(line.contains("off") && line.contains("cli"), "{line}");
        // The joint redundancy attribution requires the DEFAULT variant; on
        // Probe the plain proof clamp must be the story either way.
        assert!(!line.contains("redundantly"), "{line}");
    }
}

#[path = "capability_ledger/auto_route_provenance_tests.rs"]
mod auto_route_provenance_tests;
#[test]
#[timeout(60_000)]
fn multiworker_routes_report_startup_plan_unavailable() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    for (route, args) in [
        ("parallel-portfolio", vec!["--parallel", "2"]),
        (
            "cube-and-conquer",
            vec!["--cube-and-conquer", "1", "--parallel", "2"],
        ),
    ] {
        let output = ay_command()
            .arg("--stats")
            .args(&args)
            .args(["--no-proof", "--no-verify-proof"])
            .arg(&input)
            .output()
            .expect("run multiworker route");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            matches!(output.status.code(), Some(0 | 10 | 20)),
            "unexpected route failure; stderr={stderr}"
        );
        assert!(
            stderr.contains(&format!(
                "c startup_capability_plan: unavailable route={route}"
            )),
            "{stderr}"
        );
        assert!(capability_lines(&stderr).is_empty(), "{stderr}");

        let json_output = ay_command()
            .arg("--stats-json")
            .args(&args)
            .args(["--no-proof", "--no-verify-proof"])
            .arg(&input)
            .output()
            .expect("run multiworker JSON route");
        let json_stderr = String::from_utf8_lossy(&json_output.stderr);
        assert!(
            matches!(json_output.status.code(), Some(0 | 10 | 20)),
            "unexpected JSON route failure; stderr={json_stderr}"
        );
        assert!(
            !json_stderr.contains("c startup_capability_plan:"),
            "{json_stderr}"
        );
        let json = stats_json(&json_stderr);
        assert_eq!(json["sat.capability_plan.available"], 0);
        assert_eq!(json["sat.capability_plan.status"], "unavailable");
        assert_eq!(json["sat.capability_plan.route"], route);
        assert!(
            json["sat.capability_plan.reason"]
                .as_str()
                .is_some_and(|reason| !reason.is_empty()),
            "{json}"
        );
    }
}
