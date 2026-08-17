// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::spawn::OutputTimeout;
use ntest::timeout;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn unique_temp_path(ext: &str) -> std::path::PathBuf {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "ay_stats_flag_output_{}_{}.{}",
        std::process::id(),
        file_id,
        ext
    ))
}

fn write_temp_smt2(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path("smt2");
    std::fs::write(&path, contents).expect("failed to write temp smt2");
    (path.clone(), CleanupGuard(path))
}

fn write_temp_cnf(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path("cnf");
    std::fs::write(&path, contents).expect("failed to write temp cnf");
    (path.clone(), CleanupGuard(path))
}

fn write_temp_opb(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path("opb");
    std::fs::write(&path, contents).expect("failed to write temp opb");
    (path.clone(), CleanupGuard(path))
}

fn temp_output_path(ext: &str) -> (std::path::PathBuf, CleanupGuard) {
    let path = unique_temp_path(ext);
    (path.clone(), CleanupGuard(path))
}

/// Assert the canonical RunStatistics envelope headers are present.
fn assert_common_stats_envelope(stderr: &str) {
    assert!(
        stderr.contains("ay.mode:"),
        "Expected ay.mode in stderr: {stderr}"
    );
    assert!(
        stderr.contains("ay.result:"),
        "Expected ay.result in stderr: {stderr}"
    );
    assert!(
        stderr.contains("ay.wall_time_ms:"),
        "Expected ay.wall_time_ms in stderr: {stderr}"
    );
    assert!(
        stderr.contains("ay.build.stamp:"),
        "Expected ay.build.stamp in stderr: {stderr}"
    );
}

/// Assert SAT-level counters are present in the envelope (SMT + DIMACS modes).
fn assert_sat_counters_in_envelope(stderr: &str) {
    assert!(
        stderr.contains("conflicts:"),
        "Expected conflicts counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("decisions:"),
        "Expected decisions counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("propagations:"),
        "Expected propagations counter in stderr: {stderr}"
    );
    assert!(
        stderr.contains("restarts:"),
        "Expected restarts counter in stderr: {stderr}"
    );
}

fn parse_stats_json_line(stderr: &str) -> serde_json::Value {
    let json_line = stderr
        .lines()
        .find(|line| line.trim_start().starts_with('{'))
        .unwrap_or_else(|| panic!("expected stats JSON line on stderr, got: {stderr}"));
    serde_json::from_str(json_line).expect("stats stderr line should be valid JSON")
}

fn stats_json_u64(parsed: &serde_json::Value, key: &str) -> u64 {
    parsed[key]
        .as_u64()
        .unwrap_or_else(|| panic!("expected numeric stats JSON key {key}: {parsed}"))
}

fn stats_json_bool(parsed: &serde_json::Value, key: &str) -> bool {
    parsed[key]
        .as_bool()
        .unwrap_or_else(|| panic!("expected boolean stats JSON key {key}: {parsed}"))
}

fn dimacs_proof_telemetry(parsed: &serde_json::Value) -> (u64, u64, u64, u64) {
    (
        stats_json_u64(parsed, "sat.proof_file_present"),
        stats_json_u64(parsed, "sat.proof_file_bytes"),
        stats_json_u64(parsed, "sat.proof_writer_additions"),
        stats_json_u64(parsed, "sat.proof_writer_deletions"),
    )
}

fn assert_dimacs_bcp_telemetry_json_shape(parsed: &serde_json::Value) {
    for key in [
        "sat.bcp_blocker_hits",
        "sat.bcp_binary_hits",
        "sat.bcp_scan_steps",
        "sat.bcp_scan_steps_binary",
        "sat.bcp_scan_steps_non_binary",
        "sat.bcp_scan_steps_learned",
        "sat.bcp_scan_steps_original",
        "sat.bcp_advance_saved_pos_enabled",
        "sat.bcp_long_saved_pos_scans",
        "sat.bcp_long_saved_pos_start_false",
        "sat.bcp_long_saved_pos_found_true",
        "sat.bcp_long_saved_pos_found_unassigned",
        "sat.bcp_long_saved_pos_no_replacement",
        "sat.bcp_len18_saved_pos_scans",
        "sat.bcp_len18_saved_pos_start_false",
        "sat.bcp_len18_saved_pos_found_true",
        "sat.bcp_len18_saved_pos_found_unassigned",
        "sat.bcp_len18_saved_pos_no_replacement",
        "sat.bcp_long_blocker_fastpath_hits",
        "sat.bcp_learned_no_replacement_saved_pos_update_enabled",
        "sat.bcp_learned_1963_fsw_gent_skip_enabled",
        "sat.bcp_learned_1963_fsw_gent_skip_candidates",
        "sat.bcp_learned_1963_fsw_gent_skip_applied",
        "sat.bcp_learned_1963_fsw_gent_skip_saved_slots",
        "sat.bcp_learned_1963_fsw_gent_skip_found_true_suffix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_true_prefix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix",
        "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_unit",
        "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_conflict",
        "sat.bcp_learned_1963_blocker_cert_elision_enabled",
        "sat.bcp_learned_1963_blocker_cert_shadow_enabled",
        "sat.bcp_learned_1963_blocker_cert_false_reject_demote_enabled",
        "sat.bcp_learned_1963_blocker_cert_candidates",
        "sat.bcp_learned_1963_blocker_cert_elisions",
        "sat.bcp_learned_1963_blocker_cert_shadow_hits",
        "sat.bcp_learned_1963_blocker_cert_shadow_mismatches",
        "sat.bcp_learned_1963_blocker_cert_populates",
        "sat.bcp_learned_1963_blocker_cert_stale_rejects",
        "sat.bcp_learned_1963_blocker_cert_false_rejects",
        "sat.bcp_learned_1963_blocker_cert_false_reject_demotions",
        "sat.bcp_learned_1963_blocker_cert_repeat_rejects",
        "sat.bcp_learned_1963_blocker_cert_elided_suffix_slots",
        "sat.bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots",
        "sat.bcp_learned_1963_blocker_cert_affected_fsw_rows",
        "sat.bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows",
    ] {
        assert!(
            parsed[key].is_u64() || parsed[key].is_boolean(),
            "expected numeric BCP telemetry stats JSON key {key}: {parsed}"
        );
    }

    for bucket in ["6_8", "9_17", "18", "19_63", "64_plus"] {
        for suffix in [
            "steps",
            "learned_steps",
            "original_steps",
            "scans",
            "found_replacement",
            "found_true",
            "found_unassigned",
            "no_replacement",
            "unit",
            "conflict",
            "learned",
            "learned_found_replacement",
            "learned_no_replacement",
            "learned_unit",
            "learned_conflict",
        ] {
            let key = format!("sat.bcp_long_scan_{bucket}_{suffix}");
            assert!(
                parsed[&key].as_u64().is_some(),
                "expected numeric BCP telemetry stats JSON key {key}: {parsed}"
            );
        }
        for suffix in ["eligible", "writes", "skipped_current", "unit", "conflict"] {
            let key = format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_{suffix}");
            assert!(
                parsed[&key].as_u64().is_some(),
                "expected numeric BCP telemetry stats JSON key {key}: {parsed}"
            );
        }
    }
}

#[cfg(not(debug_assertions))]
fn assert_dimacs_bcp_telemetry_zero(parsed: &serde_json::Value) {
    assert_dimacs_bcp_telemetry_json_shape(parsed);

    for key in [
        "sat.bcp_blocker_hits",
        "sat.bcp_binary_hits",
        "sat.bcp_scan_steps",
        "sat.bcp_scan_steps_binary",
        "sat.bcp_scan_steps_non_binary",
        "sat.bcp_scan_steps_learned",
        "sat.bcp_scan_steps_original",
        "sat.bcp_advance_saved_pos_enabled",
        "sat.bcp_long_saved_pos_scans",
        "sat.bcp_long_saved_pos_start_false",
        "sat.bcp_long_saved_pos_found_true",
        "sat.bcp_long_saved_pos_found_unassigned",
        "sat.bcp_long_saved_pos_no_replacement",
        "sat.bcp_len18_saved_pos_scans",
        "sat.bcp_len18_saved_pos_start_false",
        "sat.bcp_len18_saved_pos_found_true",
        "sat.bcp_len18_saved_pos_found_unassigned",
        "sat.bcp_len18_saved_pos_no_replacement",
        "sat.bcp_long_blocker_fastpath_hits",
        "sat.bcp_learned_1963_fsw_gent_skip_candidates",
        "sat.bcp_learned_1963_fsw_gent_skip_applied",
        "sat.bcp_learned_1963_fsw_gent_skip_saved_slots",
        "sat.bcp_learned_1963_fsw_gent_skip_found_true_suffix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_true_prefix",
        "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix",
        "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_unit",
        "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_conflict",
        "sat.bcp_learned_1963_blocker_cert_candidates",
        "sat.bcp_learned_1963_blocker_cert_elisions",
        "sat.bcp_learned_1963_blocker_cert_shadow_hits",
        "sat.bcp_learned_1963_blocker_cert_shadow_mismatches",
        "sat.bcp_learned_1963_blocker_cert_populates",
        "sat.bcp_learned_1963_blocker_cert_stale_rejects",
        "sat.bcp_learned_1963_blocker_cert_false_rejects",
        "sat.bcp_learned_1963_blocker_cert_false_reject_demotions",
        "sat.bcp_learned_1963_blocker_cert_repeat_rejects",
        "sat.bcp_learned_1963_blocker_cert_elided_suffix_slots",
        "sat.bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots",
        "sat.bcp_learned_1963_blocker_cert_affected_fsw_rows",
        "sat.bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows",
    ] {
        assert_eq!(
            stats_json_u64(parsed, key),
            0,
            "BCP telemetry key {key} should stay zero without AY_BCP_TELEMETRY: {parsed}"
        );
    }

    for bucket in ["6_8", "9_17", "18", "19_63", "64_plus"] {
        for suffix in [
            "steps",
            "learned_steps",
            "original_steps",
            "scans",
            "found_replacement",
            "found_true",
            "found_unassigned",
            "no_replacement",
            "unit",
            "conflict",
            "learned",
            "learned_found_replacement",
            "learned_no_replacement",
            "learned_unit",
            "learned_conflict",
        ] {
            let key = format!("sat.bcp_long_scan_{bucket}_{suffix}");
            assert_eq!(
                stats_json_u64(parsed, &key),
                0,
                "BCP telemetry key {key} should stay zero without AY_BCP_TELEMETRY: {parsed}"
            );
        }
        for suffix in ["eligible", "writes", "skipped_current", "unit", "conflict"] {
            let key = format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_{suffix}");
            assert_eq!(
                stats_json_u64(parsed, &key),
                0,
                "BCP telemetry key {key} should stay zero without AY_BCP_TELEMETRY: {parsed}"
            );
        }
    }

    for key in [
        "sat.bcp_learned_1963_fsw_gent_skip_enabled",
        "sat.bcp_learned_1963_blocker_cert_elision_enabled",
        "sat.bcp_learned_1963_blocker_cert_shadow_enabled",
        "sat.bcp_learned_1963_blocker_cert_false_reject_demote_enabled",
    ] {
        assert!(
            !stats_json_bool(parsed, key),
            "BCP blocker-cert gate {key} should stay disabled by default: {parsed}"
        );
    }
}

fn assert_pb_native_helper_applications_match_feature(parsed: &serde_json::Value) -> u64 {
    let helper_apps = parsed["pb_native_code_helper_applications"]
        .as_u64()
        .expect("PB native-helper applications should be numeric");
    {
        assert_eq!(
            helper_apps, 0,
            "default PB solve should not report native-helper applications: {parsed}"
        );
    }
    helper_apps
}

fn assert_no_retired_sat_propagation_json_keys(parsed: &serde_json::Value) {
    let retired_keys: Vec<_> = parsed
        .as_object()
        .expect("stats JSON should be an object")
        .keys()
        .filter(|key| {
            key.contains("retired_propagation_compiler")
                || key.starts_with("sat.propagation_native_")
        })
        .cloned()
        .collect();
    assert!(
        retired_keys.is_empty(),
        "retired SAT propagation compiler counters must not appear in stats JSON: {retired_keys:?}; {parsed}"
    );
}

fn clear_competition_jit_env(command: &mut Command) {
    for name in [
        "AY_COMPETITION_TRACK",
        "AY_COMPETITION_JIT_ARTIFACT",
        "AY_COMPETITION_JIT_CANDIDATE_MODE",
        "AY_COMPETITION_JIT_APPLICATION_COUNTER",
        "AY_COMPETITION_JIT_MODE",
    ] {
        command.env_remove(name);
    }
}

#[test]
#[timeout(30_000)]
fn test_cli_stats_flag_prints_statistics_after_check_sat() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    // SMT-LIB statistics go to stderr (via safe_eprintln).
    assert!(
        stderr.contains(":conflicts"),
        "Expected SMT-LIB statistics in stderr: {stderr}"
    );
    assert!(
        stderr.contains(":num-assertions"),
        "Expected assertion count in stderr stats: {stderr}"
    );

    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
    assert!(
        !stderr.contains("dimacs-sat"),
        "SMT run should not be tagged dimacs-sat: {stderr}"
    );
    assert!(
        stderr.contains("smt.theory_conflicts:"),
        "Expected SMT theory conflicts key in stderr: {stderr}"
    );
    assert!(
        stderr.contains("smt.theory_propagations:"),
        "Expected SMT theory propagations key in stderr: {stderr}"
    );
}

#[test]
// A freshly linked macOS binary can spend minutes in first-launch validation
// before `main`. Warm the exact test binary under its own process-group timeout
// so that cost stays outside the two soundness assertions' effective budgets.
// The outer timeout exceeds 180s + 2*30s and therefore never detaches a worker
// that can still own an `ay` child.
#[timeout(300_000)]
fn test_cli_stats_authenticates_checked_projection_sat() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic UFBV)
(declare-fun plain_projection ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (= x y) (= (plain_projection y x) y))))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let warmup = Command::new(ay_path)
        .arg("--version")
        .output_timeout(Duration::from_secs(180))
        .expect("failed to warm the freshly linked ay binary");
    assert!(
        warmup.status.success(),
        "ay --version warmup failed: {:?}; stderr={}",
        warmup.status,
        String::from_utf8_lossy(&warmup.stderr)
    );

    for self_check in [false, true] {
        let mut command = Command::new(ay_path);
        command.arg("-st");
        if self_check {
            command.arg("--self-check");
        }
        let output = command
            .arg(&temp_path)
            .output_timeout(Duration::from_secs(30))
            .expect("failed to spawn ay");

        assert!(
            output.status.success(),
            "Expected zero exit status in self_check={self_check}, got {:?}",
            output.status
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            stdout.lines().next(),
            Some("sat"),
            "self_check={self_check}: {stdout}"
        );

        let stderr = String::from_utf8_lossy(&output.stderr);
        let certificate_lines: Vec<_> = stderr
            .lines()
            .filter(|line| {
                line.trim_start()
                    .starts_with("c model_validation.checked_projection_certificate:")
            })
            .collect();
        assert_eq!(
            certificate_lines.len(),
            1,
            "self_check={self_check}: the canonical statistics envelope must expose exactly one checked-projection certificate counter: {stderr}"
        );
        assert_eq!(
            certificate_lines[0]
                .strip_prefix("c model_validation.checked_projection_certificate:")
                .map(str::trim),
            Some("1"),
            "self_check={self_check}: the SAT verdict must carry exactly one checked-projection certificate: {stderr}"
        );
    }
}

#[test]
#[timeout(30_000)]
fn test_cli_without_stats_flag_omits_statistics_output() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    assert!(
        !stdout.contains(":conflicts"),
        "Did not expect SMT-LIB statistics without --stats: {stdout}"
    );
    assert!(
        !stderr.contains("ay.mode:"),
        "Did not expect canonical stats envelope without --stats: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_stats_flag_prints_statistics_on_piped_stdin() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;

    let mut child = Command::new(ay_path)
        .arg("--stats")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");

    {
        use std::io::Write;
        let stdin = child.stdin.as_mut().expect("missing child stdin");
        stdin
            .write_all(input.as_bytes())
            .expect("failed to write SMT input to stdin");
    }

    let output = child.wait_with_output().expect("failed waiting for ay");
    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(first_line, "sat", "Expected first line to be sat: {stdout}");
    // SMT-LIB statistics go to stderr (via safe_eprintln).
    assert!(
        stderr.contains(":conflicts"),
        "Expected SMT-LIB statistics in stderr: {stderr}"
    );
    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_flag_prints_statistics_to_stderr() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.contains("s SATISFIABLE"),
        "Expected SAT result on stdout: {stdout}"
    );
    assert_common_stats_envelope(&stderr);
    assert_sat_counters_in_envelope(&stderr);
    assert!(
        stderr.contains("dimacs-sat"),
        "Expected DIMACS mode tag in stderr: {stderr}"
    );
    assert!(
        stderr.contains("sat.learned_clauses:"),
        "Expected SAT-specific learned clauses key in stderr: {stderr}"
    );
    assert!(
        !stderr.contains("retired SAT propagation compiler")
            && !stderr.contains("retired_propagation_compiler")
            && !stderr.contains("sat.propagation_native_"),
        "Retired SAT propagation compiler stats must not appear in active stats output: {stderr}"
    );
    assert!(
        !stderr.contains("trail_blocked"),
        "Retired trail-blocking stats must not appear in active stats output: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_exposes_sat_attribution_keys() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let mut command = Command::new(ay_path);
    command
        .arg("--stats-json")
        .arg(&temp_path)
        .env_remove("AY_SAT_COMPETITION_PROFILE")
        .env_remove("AY_SAT_PROFILE_ID")
        .env_remove("AY_COMPETITION_JIT_MODE")
        .env_remove("AY_SAT_TRACK")
        .env_remove("AY_SAT_AI_CLASS")
        .env_remove("AY_SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE")
        .env_remove("AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION")
        .env_remove("AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW")
        .env_remove("AY_SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE")
        .env_remove("AY_BCP_TELEMETRY");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on DIMACS fixture");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert!(
        parsed.get("sat.trail_blocked_restarts").is_none(),
        "retired trail-blocking counter must not reappear in stats JSON: {parsed}"
    );
    assert!(
        stats_json_bool(&parsed, "sat.bcp_trail_lookahead_prefetch_enabled"),
        "outer-loop BCP trail-lookahead prefetch should default on: {parsed}"
    );
    let (proof_file_present, proof_file_bytes, _proof_additions, _proof_deletions) =
        dimacs_proof_telemetry(&parsed);
    // Proof-carrying is on by default (859bc49c extended the long-standing
    // DIMACS <input>.drat default; a7b73ac8 made batteries-included the CLI
    // default), so the online proof writer may legitimately record additions
    // during search even when the verdict ends up SAT. The invariant to
    // protect is that a non-UNSAT verdict leaves NO proof sidecar behind.
    assert_eq!(
        (proof_file_present, proof_file_bytes),
        (0, 0),
        "SAT DIMACS run must not leave a proof sidecar or report its bytes: {parsed}"
    );
    assert_dimacs_bcp_telemetry_json_shape(&parsed);
    for key in [
        "sat.reduction_l0_satisfied_occ_scans",
        "sat.reduction_l0_satisfied_full_scans",
        "sat.reduction_l0_satisfied_no_occ_skips",
        "sat.reduction_l0_satisfied_deleted",
        "sat.learned_reduction_considered",
        "sat.learned_reduction_deleted",
        "sat.learned_reduction_reason_protected",
        "sat.learned_reduction_ic3_protected",
        "sat.learned_reduction_low_lbd_protected",
        "sat.learned_reduction_usage_protected",
        "sat.learned_reduction_target_kept",
        "sat.learned_reduction_lrat_retained_delete_skips",
        "sat.learned_reduction_hyper_deleted",
        "sat.learned_reduction_hyper_kept",
        "sat.inproc_subsume_attempts",
        "sat.inproc_subsume_runs",
        "sat.inproc_subsume_yields",
        "sat.inproc_probe_attempts",
        "sat.inproc_probe_runs",
        "sat.inproc_probe_yields",
        "sat.inprocessing_yield_productivity_rescue_enabled",
        "sat.backbone_schedule_enabled",
        "sat.backbone_due",
        "sat.backbone_phases",
        "sat.backbone_max_rounds",
        "sat.backbone_consecutive_empty",
        "sat.backbone_stall_limit",
        "sat.backbone_stalled_by_empty",
        "sat.backbone_rounds_exhausted",
        "sat.backbone_next_conflict",
        "sat.backbone_conflicts_until_next",
        "sat.backbone_backoff_interval",
        "sat.backbone_base_interval",
        "sat.backbone_max_interval",
    ] {
        assert!(
            parsed[key].as_u64().is_some(),
            "expected numeric stats JSON key {key}: {parsed}"
        );
    }
    assert_eq!(
        stats_json_u64(
            &parsed,
            "sat.inprocessing_yield_productivity_rescue_enabled"
        ),
        0,
        "the #9084 yield-productivity rescue must stay default-off without env opt-in: {parsed}"
    );
    assert!(
        parsed["sat_native_code_helper_applications"]
            .as_u64()
            .is_some(),
        "expected SAT native-helper application counter in stats JSON: {parsed}"
    );
    for key in [
        "solver_program.sat_whole_loop.installs",
        "solver_program.sat_whole_loop.applies",
    ] {
        assert!(
            parsed[key].as_u64().is_some(),
            "expected SAT whole-loop guard counter in stats JSON key {key}: {parsed}"
        );
    }
    assert_no_retired_sat_propagation_json_keys(&parsed);
    assert_eq!(parsed["competition_jit"]["track"], "sat");
    assert_eq!(
        parsed["competition_jit"]["artifact_id"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["key"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["value"],
        parsed["sat_native_code_helper_applications"]
    );
    assert_eq!(parsed["competition_track"], "sat");
    assert_eq!(
        parsed["competition_jit_artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(parsed["competition_jit_mode"], "off");
    assert_eq!(
        parsed["competition_jit_application_counter"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "off");
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert_eq!(parsed["sat_competition"]["metadata_present"], false);
    assert_eq!(parsed["sat_competition"]["fail_closed"], true);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_sat_with_proof_cleans_non_unsat_sidecar_before_stats() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_output_path("lrat");

    let output = Command::new(ay_path)
        .arg("--stats-json")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --stats-json --proof on SAT DIMACS fixture");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !proof_path.exists(),
        "SAT proof-mode DIMACS run must remove non-UNSAT sidecar {}",
        proof_path.display()
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(parsed["result"], "sat");
    let (proof_file_present, proof_file_bytes, _proof_additions, _proof_deletions) =
        dimacs_proof_telemetry(&parsed);
    assert_eq!(
        (proof_file_present, proof_file_bytes),
        (0, 0),
        "SAT proof-mode stats must not report a stale proof sidecar: {parsed}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_trail_lookahead_prefetch_env_gate() {
    fn run_case(ay_path: &str, disable_trail_lookahead: bool) -> serde_json::Value {
        let cnf = "p cnf 2 2\n1 0\n2 0\n";
        let (temp_path, _cleanup) = write_temp_cnf(cnf);

        let mut command = Command::new(ay_path);
        command
            .arg("--stats-json")
            .arg(&temp_path)
            .env_remove("AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH")
            .env_remove("AY_SAT_COMPETITION_PROFILE")
            .env_remove("AY_SAT_PROFILE_ID")
            .env_remove("AY_COMPETITION_JIT_MODE")
            .env_remove("AY_SAT_TRACK")
            .env_remove("AY_SAT_AI_CLASS");
        if disable_trail_lookahead {
            command.env("AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH", "1");
        }

        let output = command
            .output()
            .expect("failed to spawn ay --stats-json on DIMACS prefetch gate fixture");
        assert_eq!(
            output.status.code(),
            Some(10),
            "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let stderr = String::from_utf8_lossy(&output.stderr);
        parse_stats_json_line(&stderr)
    }

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let default = run_case(ay_path, false);
    assert!(
        stats_json_bool(&default, "sat.bcp_trail_lookahead_prefetch_enabled"),
        "prefetch gate should default on: {default}"
    );

    let disabled = run_case(ay_path, true);
    assert!(
        !stats_json_bool(&disabled, "sat.bcp_trail_lookahead_prefetch_enabled"),
        "env gate should disable only outer-loop trail-lookahead prefetch: {disabled}"
    );
}

#[test]
#[cfg(not(debug_assertions))]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_bcp_telemetry_requires_explicit_env() {
    fn run_case(ay_path: &str, telemetry_enabled: bool) -> serde_json::Value {
        let cnf = "p cnf 3 4\n2 0\n1 0\n-1 2 0\n-1 3 0\n";
        let (temp_path, _cleanup) = write_temp_cnf(cnf);

        let mut command = Command::new(ay_path);
        command
            .arg("--stats-json")
            .arg("--disable")
            .arg("preprocess,walk,warmup")
            .arg(&temp_path)
            .env_remove("AY_BCP_TELEMETRY")
            .env_remove("AY_SAT_BCP_ADVANCE_SAVED_POS")
            .env_remove("AY_SAT_COMPETITION_PROFILE")
            .env_remove("AY_SAT_PROFILE_ID")
            .env_remove("AY_COMPETITION_JIT_MODE")
            .env_remove("AY_SAT_TRACK")
            .env_remove("AY_SAT_AI_CLASS");
        if telemetry_enabled {
            command.env("AY_BCP_TELEMETRY", "1");
        }

        let output = command
            .output()
            .expect("failed to spawn ay --stats-json on DIMACS BCP telemetry fixture");

        assert_eq!(
            output.status.code(),
            Some(10),
            "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );

        let stderr = String::from_utf8_lossy(&output.stderr);
        parse_stats_json_line(&stderr)
    }

    let ay_path = env!("CARGO_BIN_EXE_ay");
    let disabled = run_case(ay_path, false);
    assert_eq!(disabled["mode"], "dimacs-sat");
    assert_dimacs_bcp_telemetry_zero(&disabled);

    let enabled = run_case(ay_path, true);
    assert_eq!(enabled["mode"], "dimacs-sat");
    assert_dimacs_bcp_telemetry_json_shape(&enabled);
    assert!(
        stats_json_u64(&enabled, "sat.bcp_blocker_hits") > 0,
        "AY_BCP_TELEMETRY=1 should collect DIMACS blocker-path BCP telemetry: {enabled}"
    );
    assert!(
        stats_json_u64(&enabled, "sat.bcp_binary_hits") > 0,
        "AY_BCP_TELEMETRY=1 should collect DIMACS binary-path BCP telemetry: {enabled}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_current_mode_zero_native_helpers_fails_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let mut command = Command::new(ay_path);
    command.arg("--stats-json").arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "current")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on DIMACS current-mode fixture");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_no_retired_sat_propagation_json_keys(&parsed);
    assert_eq!(parsed["sat_native_code_helper_applications"], 0);
    assert_eq!(parsed["competition_track"], "sat");
    assert_eq!(
        parsed["competition_jit_artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(parsed["competition_jit_mode"], "current");
    assert_eq!(
        parsed["competition_jit_application_counter"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["track"], "sat");
    assert_eq!(
        parsed["competition_jit"]["artifact_id"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["key"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["application_counter"]["value"], 0);
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "current");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert_eq!(parsed["sat_competition"]["profile"], "regular");
    assert_eq!(
        parsed["sat_competition"]["profile_identity"],
        "ay-sat-regular-main"
    );
    assert_eq!(parsed["sat_competition"]["metadata_present"], true);
    assert_eq!(parsed["sat_competition"]["fail_closed"], true);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_current_mode_conflict_helper_native_applications() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let mut command = Command::new(ay_path);
    command
        .arg("--stats-json")
        .arg("--disable")
        .arg("preprocess,walk,warmup")
        .arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "current")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on DIMACS native-helper fixture");

    assert_eq!(
        output.status.code(),
        Some(20),
        "Expected UNSAT exit code 20, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let helper_apps = parsed["sat_native_code_helper_applications"]
        .as_u64()
        .expect("SAT native-helper applications should be numeric");
    let conflict_apps = parsed["sat.conflict_analysis_native_applications"]
        .as_u64()
        .expect("SAT conflict-analysis native applications should be numeric");

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert!(
        helper_apps > 0,
        "expected current-mode SAT native helper applications: {parsed}"
    );
    assert!(
        conflict_apps > 0,
        "expected conflict-analysis native helper applications: {parsed}"
    );
    assert!(
        helper_apps >= conflict_apps,
        "flat helper counter should include conflict-analysis applications: {parsed}"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["key"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["value"],
        helper_apps
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "current");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], true);
    assert_eq!(parsed["competition_jit"]["fail_closed"], false);
    assert_eq!(parsed["sat_competition"]["metadata_present"], true);
    assert_eq!(parsed["sat_competition"]["fail_closed"], false);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_current_mode_disable_jit_fails_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let mut command = Command::new(ay_path);
    command
        .arg("--stats-json")
        .arg("--disable")
        .arg("jit,preprocess,walk,warmup")
        .arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "current")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json with native helpers disabled");

    assert_eq!(
        output.status.code(),
        Some(20),
        "Expected UNSAT exit code 20, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(parsed["sat_native_code_helper_applications"], 0);
    assert_eq!(parsed["sat.conflict_analysis_native_applications"], 0);
    assert_eq!(parsed["sat.native_code_helpers_enabled"], 0);
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "current");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert_eq!(parsed["sat_competition"]["metadata_present"], true);
    assert_eq!(parsed["sat_competition"]["fail_closed"], true);
}

#[test]
#[timeout(60_000)]
fn test_cli_dimacs_stats_json_satcomp_lrat_route_exposes_native_helper_metadata() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_output_path("lrat");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--stats-json")
        .arg("--sat-variant")
        .arg("default")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&temp_path)
        .env("AY_SAT_COMPETITION_PROFILE", "regular")
        .env("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        .env("AY_COMPETITION_JIT_MODE", "off")
        .env("AY_SAT_TRACK", "main")
        .env("AY_SAT_AI_CLASS", "regular")
        .env("AY_SAT_HARD_TAIL_ROW_ID", "Circuit_multiplier22")
        .env_remove("AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT")
        .output()
        .expect("failed to spawn ay solve --stats-json on SAT-COMP DIMACS route");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout, "s SATISFIABLE\nv 1 2 0\n",
        "SAT-COMP LRAT route stdout changed"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert!(
        !proof_path.exists(),
        "SAT-COMP LRAT SAT route must remove non-UNSAT proof sidecar {}",
        proof_path.display()
    );
    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(
        dimacs_proof_telemetry(&parsed),
        (0, 0, 0, 0),
        "SAT-COMP LRAT SAT route should not retain proof sidecar evidence: {parsed}"
    );
    assert!(
        parsed["sat_native_code_helper_applications"]
            .as_u64()
            .is_some(),
        "expected SAT native-helper application counter in stats JSON: {parsed}"
    );
    assert_eq!(parsed["competition_jit"]["track"], "sat");
    assert_eq!(
        parsed["competition_jit"]["artifact_id"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["key"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"]["value"],
        parsed["sat_native_code_helper_applications"]
    );
    assert_eq!(parsed["competition_track"], "sat");
    assert_eq!(
        parsed["competition_jit_artifact"],
        "sat-native-code-helpers"
    );
    assert_eq!(parsed["competition_jit_mode"], "off");
    assert_eq!(
        parsed["competition_jit_application_counter"],
        "sat_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "off");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "off");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], false);
    assert_eq!(parsed["sat_competition"]["profile"], "regular");
    assert_eq!(
        parsed["sat_competition"]["profile_identity"],
        "ay-sat-regular-main"
    );
    assert_eq!(parsed["hard_tail_row_id"], "Circuit_multiplier22");
    assert_eq!(
        parsed["sat_competition"]["hard_tail_row_id"],
        "Circuit_multiplier22"
    );
    assert_eq!(parsed["sat_competition"]["fallback"], "scalar-cdcl-2wl");
    assert_eq!(
        parsed["sat_competition"]["route_profile"],
        "official-satcomp-main-lrat"
    );
    assert_eq!(parsed["sat_competition"]["metadata_present"], true);
    assert_eq!(parsed["sat_competition"]["fail_closed"], false);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_exposes_reduction_telemetry_keys() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 2\n1 0\n2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);

    let output = Command::new(ay_path)
        .arg("--stats-json")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --stats-json on DIMACS fixture");

    assert_eq!(
        output.status.code(),
        Some(10),
        "Expected SAT exit code 10, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let json_line = stderr
        .lines()
        .find(|line| line.trim_start().starts_with('{'))
        .unwrap_or_else(|| panic!("expected DIMACS stats JSON line on stderr, got: {stderr}"));
    let parsed: serde_json::Value =
        serde_json::from_str(json_line).expect("DIMACS stats stderr line should be valid JSON");

    assert_eq!(parsed["mode"], "dimacs-sat");
    for key in [
        "sat.reduction_l0_satisfied_occ_scans",
        "sat.reduction_l0_satisfied_full_scans",
        "sat.reduction_l0_satisfied_no_occ_skips",
        "sat.reduction_l0_satisfied_deleted",
        "sat.learned_reduction_considered",
        "sat.learned_reduction_deleted",
        "sat.learned_reduction_reason_protected",
        "sat.learned_reduction_ic3_protected",
        "sat.learned_reduction_low_lbd_protected",
        "sat.learned_reduction_usage_protected",
        "sat.learned_reduction_target_kept",
        "sat.learned_reduction_lrat_retained_delete_skips",
        "sat.learned_reduction_hyper_deleted",
        "sat.learned_reduction_hyper_kept",
    ] {
        assert!(
            parsed[key].as_u64().is_some(),
            "expected numeric stats JSON key {key}: {parsed}"
        );
    }
    for stem in [
        "decompose",
        "htr",
        "subsume",
        "probe",
        "backbone",
        "congruence",
        "bve",
        "factor",
        "sbva",
        "bce",
        "cce",
        "condition",
        "transred",
        "sweep",
        "vivify",
        "reorder",
    ] {
        for suffix in ["ms", "attempts", "runs", "yields"] {
            let key = format!("sat.inproc_{stem}_{suffix}");
            assert!(
                parsed[&key].as_u64().is_some(),
                "expected numeric stats JSON key {key}: {parsed}"
            );
        }
    }
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_dimacs_stats_json_exposes_lrat_materialization_keys() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let cnf = "p cnf 2 3\n1 0\n-1 2 0\n-1 -2 0\n";
    let (temp_path, _cleanup) = write_temp_cnf(cnf);
    let (proof_path, _proof_cleanup) = temp_output_path("lrat");

    let output = Command::new(ay_path)
        .arg("--stats-json")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --stats-json on DIMACS LRAT fixture");

    assert_eq!(
        output.status.code(),
        Some(20),
        "Expected UNSAT exit code 20, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(parsed["result"], "unsat");
    let (proof_file_present, proof_file_bytes, proof_additions, proof_deletions) =
        dimacs_proof_telemetry(&parsed);
    assert_eq!(
        proof_file_present, 1,
        "UNSAT LRAT run should report a proof file: {parsed}"
    );
    assert!(
        proof_file_bytes > 0,
        "UNSAT LRAT run should report non-empty proof bytes: {parsed}"
    );
    assert!(
        proof_additions > 0,
        "UNSAT LRAT run should report proof additions: {parsed}"
    );
    assert_eq!(
        proof_deletions, 0,
        "small LRAT fixture should not report proof deletions: {parsed}"
    );
    for (key, expected) in [
        ("sat.lrat_materialize_calls", 1),
        ("sat.lrat_materialize_minimize_calls", 0),
        ("sat.lrat_materialize_root_trail_entries", 2),
        ("sat.lrat_materialize_minimize_root_trail_entries", 0),
        ("sat.lrat_materialize_emitted_unit_lines", 1),
        ("sat.lrat_materialize_minimize_emitted_unit_lines", 0),
        ("sat.lrat_materialize_unit_hints", 2),
        ("sat.lrat_materialize_minimize_unit_hints", 0),
        ("sat.lrat_materialize_unit_max_hints", 2),
        ("sat.lrat_materialize_minimize_unit_max_hints", 0),
        ("sat.lrat_materialize_incomplete_chains", 0),
        ("sat.lrat_materialize_minimize_incomplete_chains", 0),
        ("sat.lrat_materialize_hidden_trusted_units", 0),
        ("sat.lrat_unit_chain_calls", 1),
        ("sat.lrat_unit_chain_root_trail_entries", 2),
        ("sat.lrat_unit_chain_hints", 2),
        ("sat.lrat_unit_chain_max_hints", 2),
        ("sat.lrat_unit_chain_missing_hints", 0),
    ] {
        assert_eq!(
            parsed[key].as_u64(),
            Some(expected),
            "unexpected stats JSON key {key}: {parsed}"
        );
    }
    assert!(
        std::fs::metadata(&proof_path)
            .map(|meta| meta.len() > 0)
            .unwrap_or(false),
        "expected non-empty LRAT proof at {}",
        proof_path.display()
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_flag_prints_wall_time_in_stderr() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag for --chc in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_without_stats_flag_omits_statistics_output() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.contains("ay.mode:"),
        "Did not expect CHC statistics without --stats: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_portfolio_stats_flag_prints_wall_time_in_stderr() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--portfolio")
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_flag_prints_pdr_counters() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    // Auto-HORN detection routes to CHC solver; verify envelope has CHC mode.
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("chc"),
        "Expected CHC mode tag for auto-HORN path in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_exposes_proof_transcript_metadata() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    // Proof-carrying is ON BY DEFAULT; this test pins the manifest shape for the
    // *no-artifact* case, so opt out of default certificate emission with
    // --no-proof (otherwise the artifact statuses become "hash-bound").
    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --chc --stats-json on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let transcript = &parsed["chc_proof_transcript"];

    assert_eq!(transcript["schema"], "ay.chc-proof-transcript/v1");
    assert_eq!(
        transcript["normalized_input_schema"],
        "ay.chc.normalized-input/v1"
    );
    assert_eq!(transcript["engine"], "portfolio");
    assert_eq!(transcript["result"], "safe");
    assert_eq!(transcript["proof_status"], "verified-invariant");
    assert_eq!(transcript["accepted_as_proof"], true);
    assert_eq!(transcript["trust_full_verifier_admissible"], false);
    assert_eq!(
        transcript["trust_full_verifier_non_admission_reason"],
        "metadata_only_missing_checked_replay_artifacts"
    );
    assert_eq!(
        transcript["admission_policy"]["cache_hit_admission"],
        "reject-non-admissible-proof-evidence"
    );
    assert_eq!(transcript["replay"]["status"], "replay-artifacts-required");
    assert_eq!(transcript["transcript"]["metadata_only"], true);
    let hash = transcript["normalized_input_sha256"]
        .as_str()
        .expect("normalized input hash should be a string");
    assert_eq!(
        hash.len(),
        64,
        "expected lowercase SHA-256 hex: {transcript}"
    );
    assert_eq!(transcript["pdr_input_sha256"], hash);
    assert!(
        transcript["normalized_input_bytes"].as_u64().unwrap_or(0) > 0,
        "normalized input byte count should be positive: {transcript}"
    );
    let manifest = &parsed["chc_evidence_manifest"];
    assert_eq!(manifest["schema"], "ay.chc-evidence-manifest/v1");
    assert_eq!(manifest["problem"]["normalized_input_sha256"], hash);
    assert_eq!(manifest["obligation_id"], format!("ay-cli:chc:{hash}"));
    assert_eq!(
        manifest["admission"]["cache_hit_admission"],
        "reject-non-admissible-proof-evidence"
    );
    assert_eq!(
        manifest["replay_evidence_binding_status"],
        "hash-bound-unchecked"
    );
    assert_eq!(
        manifest["artifacts"]["solver_transcript"]["status"],
        "missing"
    );
    assert_eq!(manifest["artifacts"]["proof"]["status"], "missing");
    assert_eq!(manifest["artifacts"]["replay_report"]["status"], "missing");
    assert_eq!(
        manifest["admission"]["key"]["problem_sha256"],
        manifest["problem"]["normalized_input_sha256"]
    );
    assert_eq!(
        manifest["admission"]["key"]["obligation_id"],
        manifest["obligation_id"]
    );
    // Runtime validation is ON BY DEFAULT (batteries included), which puts the
    // CHC portfolio in strict-proof mode. --competition / --no-validate would
    // restore the plain "portfolio" mode.
    assert_eq!(manifest["options"]["proof_mode"], "portfolio-strict");
    assert!(
        manifest["options"]["memory_limit_bytes"].is_u64(),
        "manifest must bind process memory limit: {manifest}"
    );
    assert!(
        manifest["solver"]["identity_sha256"]
            .as_str()
            .is_some_and(|value| value.len() == 64),
        "manifest must bind solver identity: {manifest}"
    );
    let reasons = manifest["admission"]["non_admission_reasons"]
        .as_array()
        .expect("manifest should carry non-admission reasons");
    for reason in [
        "metadata_only_missing_checked_replay_artifacts",
        "missing_solver_transcript_artifact",
        "missing_proof_artifact",
        "missing_checked_replay_report",
    ] {
        assert!(
            reasons.iter().any(|entry| entry == reason),
            "missing {reason} in {reasons:?}"
        );
    }
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_exposes_multi_cell_symbolic_array_scalarization() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv ((Array Int Int) Int) Bool)
(assert (forall ((a (Array Int Int)) (i Int))
    (=> (and (= (select a i) 0) (= (select a (+ i 1)) 1)) (Inv a i))))
(assert (forall ((a (Array Int Int)) (i Int))
    (=> (and (Inv a i) (not (= (select a (+ i 1)) 1))) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);
    let (trace_path, _trace_cleanup) = temp_output_path("jsonl");

    let mut command = Command::new(ay_path);
    command
        .arg("--chc")
        .arg("--stats-json")
        .arg("--trace-file")
        .arg(&trace_path)
        .arg(&temp_path);
    clear_competition_jit_env(&mut command);
    let output = command
        .output()
        .expect("failed to spawn ay --chc --stats-json on multi-cell symbolic array fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    assert_eq!(
        stats_json_u64(&parsed, "chc.symbolic_scalarization_projected_cells"),
        2
    );
    assert_eq!(
        stats_json_u64(&parsed, "chc.symbolic_scalarization_multi_cell_args"),
        1
    );
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_binds_emitted_certificate_artifact_hashes() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);
    let (proof_path, _proof_cleanup) = temp_output_path("chccert");

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--stats-json")
        .arg("--proof")
        .arg(&proof_path)
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --chc --stats-json --proof on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let manifest = &parsed["chc_evidence_manifest"];
    let proof = &manifest["artifacts"]["proof"]["artifact"];

    assert_eq!(manifest["artifacts"]["proof"]["status"], "hash-bound");
    assert_eq!(
        manifest["admission"]["proof_artifact_sha256"],
        proof["sha256"]
    );
    // The manifest records the canonicalized artifact path; canonicalize the
    // requested path for comparison (macOS TMPDIR lives behind a /var ->
    // /private/var symlink).
    assert_eq!(
        std::path::Path::new(proof["path"].as_str().expect("proof artifact path string")),
        std::fs::canonicalize(&proof_path)
            .expect("canonicalize requested proof path")
            .as_path(),
        "proof artifact path should name the emitted certificate"
    );
    assert!(
        proof["bytes"].as_u64().unwrap_or(0) > 0,
        "proof artifact must hash nonempty certificate bytes: {manifest}"
    );
    assert_eq!(
        proof["sha256"].as_str().map(str::len),
        Some(64),
        "proof artifact must carry lowercase SHA-256: {manifest}"
    );
    assert_eq!(
        manifest["artifacts"]["replay_obligations"]["status"],
        "hash-bound"
    );
    assert!(
        manifest["artifacts"]["replay_obligations"]["artifacts"]
            .as_array()
            .is_some_and(|artifacts| {
                !artifacts.is_empty()
                    && artifacts
                        .iter()
                        .all(|artifact| artifact["kind"].as_str().is_some())
            }),
        "safe CHC certificate should emit typed replay obligation artifacts: {manifest}"
    );
    assert_eq!(
        manifest["artifacts"]["replay_report"]["status"], "missing",
        "CLI hashes emitted artifacts but still requires an actual checked replay report"
    );
    assert_eq!(
        manifest["admission"]["cache_hit_admission"],
        "reject-non-admissible-proof-evidence"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_binds_unsafe_trace_validity_obligation_hash() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);
    let (proof_path, _proof_cleanup) = temp_output_path("chccert");

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--stats-json")
        .arg("--proof")
        .arg(&proof_path)
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay --chc --stats-json --proof on unsafe CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let manifest = &parsed["chc_evidence_manifest"];
    let obligations = manifest["artifacts"]["replay_obligations"]["artifacts"]
        .as_array()
        .expect("unsafe CHC replay obligations should be an array");
    let trace_obligation = obligations
        .iter()
        .find(|artifact| {
            artifact["kind"].as_str() == Some("trace-validity")
                && artifact["path"]
                    .as_str()
                    .is_some_and(|path| path.contains("trace-validity"))
        })
        .unwrap_or_else(|| panic!("missing trace-validity obligation: {manifest}"));
    let trace_path = trace_obligation["path"]
        .as_str()
        .expect("trace obligation path should be recorded");
    let trace_query =
        std::fs::read_to_string(trace_path).expect("trace-validity query should exist");

    assert_eq!(manifest["result"]["result"], "unsafe");
    assert_eq!(
        manifest["artifacts"]["replay_obligations"]["status"],
        "hash-bound"
    );
    assert_eq!(
        trace_obligation["sha256"].as_str().map(str::len),
        Some(64),
        "trace-validity query should be hash-bound: {manifest}"
    );
    assert!(
        trace_query.contains("; expected-result: sat")
            && trace_query.contains("; kind: trace-validity"),
        "trace-validity query should be self-describing: {trace_query}"
    );

    let check_query = |path: &std::path::Path, expected: &str, label: &str| {
        let output = Command::new(ay_path)
            .arg(path)
            .output()
            .unwrap_or_else(|error| panic!("failed to spawn ay for {label}: {error}"));
        assert!(
            output.status.success(),
            "{label} checker process failed with {:?}; stdout={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            stdout
                .lines()
                .find(|line| !line.trim().is_empty())
                .map(str::trim),
            Some(expected),
            "{label} expected {expected}; stdout={stdout} stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    check_query(
        std::path::Path::new(trace_path),
        "sat",
        "emitted trace-validity",
    );

    let (prefix, suffix) = trace_query
        .rsplit_once("(= v0_1 1)")
        .expect("trace-validity query should bind the final trace assignment");
    let corrupted_trace_query = format!("{prefix}(= v0_1 2){suffix}");
    let (corrupted_trace_path, _corrupted_trace_cleanup) = temp_output_path("smt2");
    std::fs::write(&corrupted_trace_path, corrupted_trace_query)
        .expect("write corrupted trace-validity query");
    check_query(
        &corrupted_trace_path,
        "unsat",
        "corrupted trace-validity assignment",
    );

    let corrupted_clause_query = trace_query.replace("(= v0_1 (+ v0 1))", "(= v0_1 (+ v0 2))");
    assert_ne!(
        corrupted_clause_query, trace_query,
        "trace-validity query should expose the transition clause"
    );
    let (corrupted_clause_path, _corrupted_clause_cleanup) = temp_output_path("smt2");
    std::fs::write(&corrupted_clause_path, corrupted_clause_query)
        .expect("write corrupted clause-sequence query");
    check_query(
        &corrupted_clause_path,
        "unsat",
        "corrupted trace-validity clause sequence",
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_counts_tla_action_profile_without_native_helper() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-rel Inv (Int Bool))
(declare-var x Int)
(declare-var ok Bool)
(rule (=> (= x 0) (Inv x true)))
(ay-declare-action Step)
(ay-action-rule Step
  (=> (and (Inv x ok) ok (< x 3))
      (Inv (+ x 1) ok)))
(query (and (Inv x ok) (>= x 10)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let mut command = Command::new(ay_path);
    command.arg("--stats-json").arg(&temp_path);
    clear_competition_jit_env(&mut command);
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let json_line = stderr
        .lines()
        .find(|line| line.trim_start().starts_with('{'))
        .unwrap_or_else(|| panic!("expected CHC stats JSON line on stderr, got: {stderr}"));
    let parsed: serde_json::Value =
        serde_json::from_str(json_line).expect("CHC stats stderr line should be valid JSON");

    let tla_profile_count = parsed["chc_tla_transition_cluster_applications"]
        .as_u64()
        .expect("TLA profile counter should be a JSON number");
    assert!(
        tla_profile_count > 0,
        "expected profile-only TLA transition-cluster counter > 0: {parsed}"
    );
    assert_eq!(parsed["chc_native_code_helper_applications"], 0);
    assert_eq!(parsed["competition_jit"]["schema_version"], 1);
    assert_eq!(parsed["competition_jit"]["track"], "chc");
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "chc-tla-transition-clusters"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "chc_tla_transition_cluster_applications"
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], false);
    assert!(
        parsed.get("ay_build").is_some(),
        "shared stats envelope should include build provenance: {parsed}"
    );
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_solver_program_tla_transition_cluster_fails_closed_without_install_apply(
) {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-rel Inv (Int Bool))
(declare-var x Int)
(declare-var ok Bool)
(rule (=> (= x 0) (Inv x true)))
(ay-declare-action Step)
(ay-action-rule Step
  (=> (and (Inv x ok) ok (< x 3))
      (Inv (+ x 1) ok)))
(query (and (Inv x ok) (>= x 10)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let mut command = Command::new(ay_path);
    command.arg("--stats-json").arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command.env("AY_COMPETITION_JIT_MODE", "solver-program");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let tla_profile_count = parsed["chc_tla_transition_cluster_applications"]
        .as_u64()
        .expect("TLA profile counter should be a JSON number");

    assert!(
        tla_profile_count > 0,
        "expected profile evidence to remain visible in solver-program mode: {parsed}"
    );
    assert_eq!(parsed["chc_native_code_helper_applications"], 0);
    assert_eq!(parsed["solver_program.tla2_transition_cluster.installs"], 0);
    assert_eq!(parsed["solver_program.tla2_transition_cluster.applies"], 0);
    assert_eq!(parsed["competition_jit"]["track"], "chc");
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "chc-tla-transition-clusters"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "chc_tla_transition_cluster_applications"
    );
    assert_eq!(
        parsed["competition_jit"]["requested_mode"],
        "solver-program"
    );
    assert_eq!(
        parsed["competition_jit"]["candidate_mode"],
        "solver-program"
    );
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_current_mode_uses_native_helper_application_counter() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-rel Inv (Int Bool))
(declare-var x Int)
(declare-var ok Bool)
(rule (=> (= x 0) (Inv x true)))
(ay-declare-action Step)
(ay-action-rule Step
  (=> (and (Inv x ok) ok (< x 3))
      (Inv (+ x 1) ok)))
(query (and (Inv x ok) (>= x 10)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let mut command = Command::new(ay_path);
    command.arg("--stats-json").arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command.env("AY_COMPETITION_JIT_MODE", "current");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let tla_profile_count = parsed["chc_tla_transition_cluster_applications"]
        .as_u64()
        .expect("TLA profile counter should be a JSON number");

    assert!(
        tla_profile_count > 0,
        "expected TLA transition-cluster profiling to remain visible: {parsed}"
    );
    assert_eq!(parsed["chc_native_code_helper_applications"], 0);
    assert_eq!(parsed["competition_jit"]["track"], "chc");
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "chc-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "chc_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "current");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_json_current_mode_reports_confirmed_native_helper_application() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((req Int) (audit Int))
    (=> (and (= req 0) (= audit 0))
        (inv req audit))))
(assert (forall ((req Int) (audit Int) (req2 Int) (audit2 Int))
    (=> (and (inv req audit)
             (= req 0)
             (= req2 1)
             (= audit2 audit))
        (inv req2 audit2))))
(assert (forall ((req Int) (audit Int) (req2 Int) (audit2 Int))
    (=> (and (inv req audit)
             (= req 1)
             (= req2 2)
             (= audit2 1))
        (inv req2 audit2))))
(assert (forall ((req Int) (audit Int))
    (=> (and (inv req audit)
             (= req 2)
             (= audit 0))
        false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let mut command = Command::new(ay_path);
    command.arg("--stats-json").arg("--chc").arg(&temp_path);
    clear_competition_jit_env(&mut command);
    command.env("AY_COMPETITION_JIT_ARTIFACT", "chc-native-code-helpers");
    command.env("AY_COMPETITION_JIT_MODE", "current");
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json --chc on CHC native-helper fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let applications = parsed["chc_native_code_helper_applications"]
        .as_u64()
        .expect("native-helper applications should be numeric");

    // This trivial Int self-loop is discharged by the portfolio's fast
    // algebraic-invariant prepass (it synthesises a sound affine invariant
    // before PDR's frame-pushing loop ever runs). The native code helper lives
    // in the PDR implication cache and is only exercised once PDR repeatedly
    // evaluates a "hot" candidate lemma, so on this input it is never compiled
    // or applied: `chc.iterations` stays 0 and every native-helper counter is
    // 0. That is the correct, sound outcome — not a JIT regression. The
    // competition-JIT fail-closed contract therefore reports no native
    // dispatch, matching the sibling
    // `test_cli_chc_stats_json_current_mode_uses_native_helper_application_counter`
    // case. (The genuine apply/confirm/trusted-true contract is covered by the
    // `ay-chc` implication-cache unit tests, which drive PDR directly.)
    assert_eq!(
        applications, 0,
        "trivial Int CHC solved by the algebraic prepass must not dispatch the native helper: {parsed}"
    );
    assert_eq!(parsed["chc.native_code_helper_applications"], applications);
    assert_eq!(parsed["chc.native_code_helper_compile_attempts"], 0);
    assert_eq!(parsed["chc.native_code_helper_compile_successes"], 0);
    assert_eq!(parsed["chc.native_code_helper_evaluations"], applications);
    assert_eq!(
        parsed["chc.native_code_helper_interpreter_confirmations"]
            .as_u64()
            .expect("interpreter confirmations should be numeric")
            + parsed["chc.native_code_helper_trusted_true_results"]
                .as_u64()
                .expect("trusted true results should be numeric"),
        applications,
        "native applications must be either interpreter-confirmed or trusted true"
    );
    assert_eq!(parsed["chc.native_code_helper_trusted_true_results"], 0);
    assert_eq!(parsed["chc.native_code_helper_deopts"], 0);
    assert_eq!(parsed["chc.native_code_helper_fallbacks"], 0);
    assert_eq!(parsed["chc.native_code_helper_missing_var_fallbacks"], 0);
    assert_eq!(parsed["chc_tla_transition_cluster_applications"], 0);
    assert_eq!(parsed["competition_jit"]["track"], "chc");
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "chc-native-code-helpers"
    );
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "current");
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn test_cli_chc_stats_json_single_engine_zero_native_helper_fail_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);
    let (trace_path, _trace_cleanup) = temp_output_path("jsonl");

    let mut command = Command::new(ay_path);
    command
        .arg("--trace-file")
        .arg(&trace_path)
        .arg("--stats-json")
        .arg(&temp_path);
    clear_competition_jit_env(&mut command);
    let output = command
        .output()
        .expect("failed to spawn ay --stats-json --trace-file on CHC fixture");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}; stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["chc_tla_transition_cluster_applications"], 0);
    assert_eq!(parsed["chc_native_code_helper_applications"], 0);
    assert_eq!(parsed["competition_jit"]["track"], "chc");
    assert_eq!(
        parsed["competition_jit"]["artifact"],
        "chc-native-code-helpers"
    );
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "chc_native_code_helper_applications"
    );
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn test_cli_chc_stats_env_var_prints_wall_time_in_stderr() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_smt2(input);

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg("--stats")
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_common_stats_envelope(&stderr);
    assert!(
        stderr.contains("portfolio"),
        "Expected portfolio mode tag with --chc + --stats in stderr: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn pb26_cli_output_pb_solve_stats_json_emits_shared_pb_counters_on_stderr() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "\
* #variable= 12 #constraint= 4
+1 x1 +1 x2 +1 x3 >= 2 ;
+1 x4 +1 x5 +1 x6 >= 2 ;
+1 x7 +1 x8 +1 x9 >= 2 ;
+1 x10 +1 x11 +1 x12 >= 2 ;
";
    let (temp_path, _cleanup) = write_temp_opb(input);

    let output = Command::new(ay_path)
        .arg("pb")
        .arg("solve")
        .arg("--stats-json")
        .arg(&temp_path)
        .env_remove("AY_COMPETITION_JIT_MODE")
        .output()
        .expect("failed to spawn ay pb solve --stats-json");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s SATISFIABLE"),
        "expected PB competition result on stdout, got: {stdout}"
    );
    assert!(
        !stdout.contains("pb_pbo_candidate_applications"),
        "stats JSON must stay on stderr, stdout was: {stdout}"
    );
    assert!(
        !stdout.contains("pb_portfolio_"),
        "portfolio timing JSON must stay on stderr, stdout was: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "pb");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["pb_pbo_candidate_applications"], 4);
    assert_eq!(
        parsed["pb_native_code_helper_applications"], 0,
        "profile-only PB route should not report solve-path native-helper applications: {parsed}"
    );
    for key in [
        "pb_portfolio_total_ms",
        "pb_portfolio_profile_ms",
        "pb_portfolio_max_clique_ms",
        "pb_portfolio_root_unsat_precheck_ms",
        "pb_portfolio_pre_native_sat_ms",
        "pb_portfolio_prefix_incumbent_ms",
        "pb_portfolio_native_ms",
        "pb_portfolio_sat_ms",
        "pb_clique_published_exact_continue",
        "pb_clique_published_exact_decision",
        "pb_clique_published_exact_exchange",
    ] {
        assert!(
            parsed[key].as_u64().is_some(),
            "expected numeric PB portfolio timing field {key}: {parsed}"
        );
    }
    assert_eq!(parsed["competition_jit"]["schema_version"], 1);
    assert_eq!(parsed["competition_jit"]["track"], "pb");
    assert_eq!(parsed["competition_jit"]["artifact"], "pb-pbo-candidates");
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "pb_pbo_candidate_applications"
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], false);
    assert!(
        parsed.get("ay_build").is_some(),
        "shared stats envelope should include build provenance: {parsed}"
    );
    assert!(
        !stderr.contains("c ay.mode:"),
        "--stats-json alone should not emit the human stats block: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn pb26_cli_output_pb_solve_stats_json_omits_portfolio_timing_for_native_route() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "\
1 x1 +1 x2 >= 1 ;
";
    let (temp_path, _cleanup) = write_temp_opb(input);

    let output = Command::new(ay_path)
        .arg("pb")
        .arg("solve")
        .arg("--native")
        .arg("--stats-json")
        .arg(&temp_path)
        .env_remove("AY_COMPETITION_JIT_MODE")
        .output()
        .expect("failed to spawn ay pb solve --native --stats-json");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("s SATISFIABLE"),
        "expected PB competition result on stdout, got: {stdout}"
    );
    assert!(
        !stdout.contains("pb_portfolio_"),
        "stats JSON must not leak portfolio timing comments to stdout: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);
    let fields = parsed.as_object().expect("stats JSON should be an object");
    assert!(
        !fields.keys().any(|key| key.starts_with("pb_portfolio_")),
        "native PB route should not report portfolio timing fields: {parsed}"
    );
}

#[test]
#[timeout(30_000)]
fn pb26_cli_output_pb_solve_stats_json_profile_only_zero_pbo_applications_fails_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "\
1 x1 >= 1 ;
";
    let (temp_path, _cleanup) = write_temp_opb(input);

    let output = Command::new(ay_path)
        .arg("pb")
        .arg("solve")
        .arg("--stats-json")
        .arg(&temp_path)
        .env_remove("AY_COMPETITION_JIT_MODE")
        .output()
        .expect("failed to spawn ay pb solve --stats-json");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "pb");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["pb_pbo_candidate_applications"], 0);
    assert_eq!(parsed["pb_native_code_helper_applications"], 0);
    assert_eq!(parsed["competition_jit"]["track"], "pb");
    assert_eq!(parsed["competition_jit"]["artifact"], "pb-pbo-candidates");
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "pb_pbo_candidate_applications"
    );
    assert_eq!(parsed["competition_jit"]["requested_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "profile-only");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
}

#[test]
#[timeout(30_000)]
fn pb26_cli_output_pb_solve_stats_json_invalid_mode_fail_closes_with_solve_path_helper_evidence() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "\
+1 x1 +1 x2 +1 x3 >= 2 ;
+1 x4 +1 x5 +1 x6 >= 2 ;
+1 x7 +1 x8 +1 x9 >= 2 ;
+1 x10 +1 x11 +1 x12 >= 2 ;
";
    let (temp_path, _cleanup) = write_temp_opb(input);

    let output = Command::new(ay_path)
        .arg("pb")
        .arg("solve")
        .arg("--stats-json")
        .arg("--native")
        .arg(&temp_path)
        .env("AY_COMPETITION_JIT_MODE", "definitely-not-a-pb-mode")
        .output()
        .expect("failed to spawn ay pb solve --stats-json --native");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "pb");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["pb_pbo_candidate_applications"], 4);
    assert_pb_native_helper_applications_match_feature(&parsed);
    assert_eq!(parsed["competition_jit"]["track"], "pb");
    assert_eq!(parsed["competition_jit"]["artifact"], "pb-pbo-candidates");
    assert_eq!(
        parsed["competition_jit"]["application_counter"],
        "pb_pbo_candidate_applications"
    );
    assert_eq!(
        parsed["competition_jit"]["requested_mode"],
        "definitely-not-a-pb-mode"
    );
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "off");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
}

#[test]
#[timeout(30_000)]
fn pb26_cli_output_pb_solve_stats_json_current_mode_counts_solve_path_helpers_fail_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let input = "\
+1 x1 +1 x2 +1 x3 >= 2 ;
+1 x4 +1 x5 +1 x6 >= 2 ;
+1 x7 +1 x8 +1 x9 >= 2 ;
+1 x10 +1 x11 +1 x12 >= 2 ;
";
    let (temp_path, _cleanup) = write_temp_opb(input);

    let output = Command::new(ay_path)
        .arg("pb")
        .arg("solve")
        .arg("--stats-json")
        .arg("--native")
        .arg(&temp_path)
        .env("AY_COMPETITION_JIT_MODE", "current")
        .output()
        .expect("failed to spawn ay pb solve --stats-json --native");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let parsed = parse_stats_json_line(&stderr);

    assert_eq!(parsed["mode"], "pb");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["pb_pbo_candidate_applications"], 4);
    let helper_apps = assert_pb_native_helper_applications_match_feature(&parsed);
    assert_eq!(parsed["competition_jit"]["track"], "pb");
    if helper_apps > 0 {
        assert_eq!(
            parsed["competition_jit"]["artifact"],
            "pb-native-code-helpers"
        );
        assert_eq!(
            parsed["competition_jit"]["application_counter"],
            "pb_native_code_helper_applications"
        );
    } else {
        assert_eq!(parsed["competition_jit"]["artifact"], "pb-pbo-candidates");
        assert_eq!(
            parsed["competition_jit"]["application_counter"],
            "pb_pbo_candidate_applications"
        );
    }
    assert_eq!(parsed["competition_jit"]["requested_mode"], "current");
    assert_eq!(parsed["competition_jit"]["candidate_mode"], "off");
    assert_eq!(parsed["competition_jit"]["native_dispatch"], false);
    assert_eq!(parsed["competition_jit"]["fail_closed"], true);
}
