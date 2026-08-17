// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn multiplier_equivalence_cnf() -> String {
    let mut cnf = String::from("p cnf 3000 9000\n1 0\n");
    for i in 0..3400 {
        let a = i % 3000 + 1;
        let b = (i + 1) % 3000 + 1;
        cnf.push_str(&format!("-{a} {b} 0\n"));
    }
    for i in 0..2299 {
        let a = i % 3000 + 1;
        let b = (i + 1) % 3000 + 1;
        let c = (i + 2) % 3000 + 1;
        cnf.push_str(&format!("-{a} -{b} {c} 0\n"));
    }
    for i in 0..3300 {
        let a = i % 3000 + 1;
        let b = (i + 1) % 3000 + 1;
        let c = (i + 2) % 3000 + 1;
        cnf.push_str(&format!("{a} {b} -{c} 0\n"));
    }
    cnf
}

fn binary_band_unsat_cnf(num_vars: usize, num_clauses: usize) -> String {
    assert!(num_vars >= 2 && num_clauses >= 3);
    let mut cnf = format!("p cnf {num_vars} {num_clauses}\n1 0\n-1 0\n");
    for i in 0..(num_clauses - 2) {
        let a = i % num_vars + 1;
        // Reach the declared high variable even when the two unit clauses
        // consume part of the clause budget. Route selection intentionally
        // uses the content-driven maximum, not the DIMACS header.
        let b = (i + 2) % num_vars + 1;
        cnf.push_str(&format!("{a} -{b} 0\n"));
    }
    cnf
}

#[test]
#[timeout(60_000)]
fn probe_route_kill_switch_is_the_decisive_buffered_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("probe-band.cnf");
    std::fs::write(&input, binary_band_unsat_cnf(50_000, 50_000)).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-probe-route")
        .output()
        .expect("run vetoed buffered probe route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(
        capability_line(&stderr, "vivify").contains("cli"),
        "{stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn aggressive_route_kill_switch_is_the_decisive_streaming_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("aggressive-band.cnf");
    std::fs::write(&input, binary_band_unsat_cnf(100_000, 600_000)).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-aggressive-route")
        .output()
        .expect("run vetoed streaming aggressive route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(stderr.contains("c streaming parse:"), "{stderr}");
    // B34: the vetoed route is an operator decision; the resulting Default
    // profile's bve state is resolved by policy, and the veto itself shows
    // on the gates whose state moved (vivify below).
    assert!(
        capability_line(&stderr, "bve").contains("resolved Default profile policy"),
        "{stderr}"
    );
    assert!(
        capability_line(&stderr, "vivify").contains("cli"),
        "{stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn probe_route_kill_switch_reaches_proof_streaming_plan() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("probe-proof.cnf");
    let proof = scratch.path().join("proof.drat");
    std::fs::write(&input, binary_band_unsat_cnf(50_000, 50_000)).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .arg(&input)
        .arg("--sat-no-probe-route")
        .output()
        .expect("run vetoed proof probe route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    assert!(
        capability_line(&stderr, "vivify").contains("cli"),
        "{stderr}"
    );
}

fn assert_combined_bve_threshold_source(
    num_vars: usize,
    num_clauses: usize,
    max_vars: &str,
    max_density: &str,
    expected_state: &str,
) {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("bve-thresholds.cnf");
    let cnf = format!("p cnf {num_vars} {num_clauses}\n1 0\n-1 0\n{num_vars} -{num_vars} 0\n");
    std::fs::write(&input, cnf).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .args(["--sat-bve-sparse-max-vars", max_vars])
        .args(["--sat-bve-sparse-max-density", max_density])
        .output()
        .expect("run combined BVE thresholds");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "bve");
    assert!(line.contains(expected_state), "{line}");
    assert!(line.contains("cli"), "{line}");
}

#[test]
#[timeout(60_000)]
fn joint_bve_thresholds_truthfully_name_disable_and_enable_sources() {
    assert_combined_bve_threshold_source(100_000, 1_000_000, "50000", "5", "off");
    assert_combined_bve_threshold_source(151_000, 1_827_100, "200000", "13", "on");
}

#[test]
#[timeout(60_000)]
fn bve_kill_and_threshold_report_combined_redundant_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("bve-kill-threshold.cnf");
    std::fs::write(
        &input,
        "p cnf 100000 1000000\n1 0\n-1 0\n100000 -100000 0\n",
    )
    .expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-bve-sparse")
        .args(["--sat-bve-sparse-max-vars", "50000"])
        .output()
        .expect("run redundant BVE kills");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "bve");
    // B34: any attribution involving the kill is a CLI decision; the joint
    // explanation still names every control.
    assert!(
        line.contains("off") && line.contains("cli") && line.contains("jointly change admission"),
        "{line}"
    );
}

#[test]
#[timeout(30_000)]
fn official_route_aliases_report_the_exact_matching_set() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.lrat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "lrat"])
        .arg(&input)
        .env(
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-lrat-v1",
        )
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .output()
        .expect("run aliased official route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "walk");
    assert!(
        line.contains(
            "env:AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_PROFILE_ID+AY_SAT_COMPETITION_PROFILE"
        ),
        "{line}"
    );
}

#[test]
#[timeout(30_000)]
fn ai_class_veto_reports_the_exact_negative_route_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.lrat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "lrat"])
        .arg(&input)
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "no-limit")
        .output()
        .expect("run vetoed official route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    for capability in ["walk", "warmup"] {
        let line = capability_line(&stderr, capability);
        assert!(
            line.contains("on") && line.contains("env:AY_SAT_AI_CLASS"),
            "{line}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn ai_class_veto_and_startup_override_report_the_combined_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("unsat.cnf");
    let proof = scratch.path().join("proof.lrat");
    std::fs::write(&input, UNSAT_CNF).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "lrat"])
        .arg(&input)
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "no-limit")
        .env("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT", "1")
        .output()
        .expect("run jointly overridden official route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    for capability in ["walk", "warmup"] {
        let line = capability_line(&stderr, capability);
        assert!(
            line.contains("on")
                && line.contains("env:AY_SAT_AI_CLASS+AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT",),
            "{line}"
        );
    }
}

#[test]
#[timeout(60_000)]
fn probe_veto_and_substitution_shims_report_joint_sources() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("probe-joint.cnf");
    std::fs::write(&input, binary_band_unsat_cnf(50_000, 50_000)).expect("write CNF");

    let killed = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-probe-route")
        .arg("--sat-no-subst-auto")
        .output()
        .expect("run joint probe/substitution kills");
    let stderr = String::from_utf8_lossy(&killed.stderr);
    assert_eq!(killed.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "decompose");
    assert!(line.contains("off") && line.contains("cli"), "{line}");
}

#[test]
#[timeout(60_000)]
fn probe_veto_and_raised_bve_ceiling_report_the_combined_source() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("probe-bve-joint.cnf");
    std::fs::write(&input, binary_band_unsat_cnf(151_001, 151_001)).expect("write CNF");
    let output = ay_command()
        .args(["--stats", "--no-proof"])
        .arg(&input)
        .arg("--sat-no-probe-route")
        .args(["--sat-bve-sparse-max-vars", "200000"])
        .output()
        .expect("run joint probe/BVE route");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(20), "stderr={stderr}");
    let line = capability_line(&stderr, "bve");
    // B34: the raised ceiling is the one env influence left on this line.
    assert!(line.contains("on") && line.contains("cli"), "{line}");
}

#[test]
#[timeout(60_000)]
fn circuit_profile_cli_truthfully_suppresses_auto_symmetry() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("multiplier.cnf");
    std::fs::write(&input, multiplier_equivalence_cnf()).expect("write CNF");

    let baseline = ay_command()
        .args(["--stats", "--no-proof", "--sat-variant", "default"])
        .arg(&input)
        .output()
        .expect("run baseline multiplier shape");
    let baseline_stderr = String::from_utf8_lossy(&baseline.stderr);
    let baseline_line = capability_line(&baseline_stderr, "symmetry");
    assert!(
        baseline_line.contains("on") && baseline_line.contains("auto"),
        "{baseline_line}"
    );

    let suppressed = ay_command()
        .args(["--stats", "--no-proof", "--sat-variant", "default"])
        .arg(&input)
        .arg("--sat-circuit-equiv-throughput-profile")
        .output()
        .expect("run suppressed multiplier shape");
    let suppressed_stderr = String::from_utf8_lossy(&suppressed.stderr);
    let suppressed_line = capability_line(&suppressed_stderr, "symmetry");
    assert!(
        suppressed_line.contains("off") && suppressed_line.contains("cli"),
        "{suppressed_line}"
    );
}

#[test]
#[timeout(60_000)]
fn proof_policy_supersedes_circuit_profile_cli_suppression() {
    let scratch = tempdir().expect("temp dir");
    let input = scratch.path().join("multiplier.cnf");
    let proof = scratch.path().join("proof.drat");
    std::fs::write(&input, multiplier_equivalence_cnf()).expect("write CNF");

    let output = ay_command()
        .args(["--stats", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "drat"])
        .arg(&input)
        .arg("--sat-circuit-equiv-throughput-profile")
        .output()
        .expect("run circuit cli under proof policy");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(10), "stderr={stderr}");
    let line = capability_line(&stderr, "symmetry");
    assert!(line.contains("off") && line.contains("auto"), "{line}");
    assert!(!line.contains("env:"), "{line}");
}
