// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::literal_string_with_formatting_args)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use tempfile::TempDir;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

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

fn run_ay(args: &[&str]) -> Output {
    Command::new(ay())
        .args(args)
        .current_dir(repo_root())
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay")
}

fn stdout_json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "stdout must be JSON: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn assert_success(output: &Output, context: &str) {
    assert!(
        output.status.success(),
        "{context} failed with {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    format!("{:x}", digest.finalize())
}

fn sha256_file(path: &Path) -> String {
    sha256_bytes(&fs::read(path).unwrap_or_else(|err| panic!("read {}: {err}", path.display())))
}

fn git_bytes(args: &[&str]) -> Vec<u8> {
    let output = Command::new("git")
        .args(args)
        .current_dir(repo_root())
        .output()
        .unwrap_or_else(|err| panic!("spawn git {args:?}: {err}"));
    assert!(
        output.status.success(),
        "git {args:?} failed with {:?}: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn git_string(args: &[&str]) -> String {
    String::from_utf8(git_bytes(args))
        .unwrap_or_else(|err| panic!("git {args:?} stdout must be utf-8: {err}"))
        .trim()
        .to_string()
}

fn write_file(path: &Path, text: &str) {
    fs::write(path, text).unwrap_or_else(|err| panic!("write {}: {err}", path.display()));
}

fn write_json_file(path: &Path, value: &Value) {
    write_file(
        path,
        &serde_json::to_string_pretty(value).expect("serialize JSON"),
    );
}

fn make_executable(path: &Path) {
    #[cfg(unix)]
    {
        let mut permissions = fs::metadata(path)
            .unwrap_or_else(|err| panic!("stat {}: {err}", path.display()))
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions)
            .unwrap_or_else(|err| panic!("chmod {}: {err}", path.display()));
    }
}

fn stale_release_report(tmp: &TempDir) -> PathBuf {
    let evidence_dir = tmp.path().join("sat-evidence");
    fs::create_dir_all(&evidence_dir)
        .unwrap_or_else(|err| panic!("create {}: {err}", evidence_dir.display()));

    let package_log = evidence_dir.join("sat-package.log");
    let replay_log = evidence_dir.join("sat-replay.log");
    let artifact = evidence_dir.join("sat-artifact.txt");
    write_file(&package_log, "package sat\n");
    write_file(&replay_log, "replay sat\n");
    write_file(&artifact, "artifact sat\n");

    let root = repo_root();
    let matrix = root.join("competition/jit_mode_matrix.json");
    let matrix_schema = root.join("competition/jit_mode_matrix.schema.json");
    let status = git_bytes(&["status", "--porcelain=v1", "--untracked-files=all"]);

    let report = json!({
        "schema": "ay.competition-jit-release-report/v1",
        "release_status": "ready",
        "track": "sat",
        "source": {
            "kind": "git-worktree",
            "git_commit": git_string(&["rev-parse", "HEAD"]),
            "git_branch": git_string(&["rev-parse", "--abbrev-ref", "HEAD"]),
            "git_dirty": !status.is_empty(),
            "git_status_sha256": sha256_bytes(&status),
            "source_tree_sha256": "0000000000000000000000000000000000000000000000000000000000000000"
        },
        "matrix": "competition/jit_mode_matrix.json",
        "matrix_sha256": sha256_file(&matrix),
        "matrix_schema": "competition/jit_mode_matrix.schema.json",
        "matrix_schema_sha256": sha256_file(&matrix_schema),
        "package": {
            "command": "package sat",
            "status": "pass",
            "exit_code": 0,
            "log": package_log,
            "log_sha256": sha256_file(&package_log),
            "artifact_path": artifact,
            "artifact_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        },
        "replay": {
            "command": "replay sat",
            "status": "pass",
            "exit_code": 0,
            "log": replay_log,
            "log_sha256": sha256_file(&replay_log)
        },
        "gate": {
            "artifact": "sat-native-code-helpers",
            "baseline": {
                "application_count": 0,
                "crashes": 0,
                "native_apply_count": null,
                "native_helper_compile_attempt_count": null,
                "native_helper_compile_success_count": null,
                "native_helper_deopt_count": null,
                "native_helper_evaluation_count": null,
                "native_helper_fallback_count": null,
                "native_helper_interpreter_confirmation_count": null,
                "native_helper_missing_var_fallback_count": null,
                "native_helper_trusted_true_count": null,
                "native_install_count": null,
                "par2": 20.0,
                "proof_failures": 0,
                "solved": 4,
                "witness_failures": 0,
                "wrong_answers": 0
            },
            "candidate": {
                "application_count": 2,
                "crashes": 0,
                "native_apply_count": null,
                "native_helper_compile_attempt_count": null,
                "native_helper_compile_success_count": null,
                "native_helper_deopt_count": null,
                "native_helper_evaluation_count": null,
                "native_helper_fallback_count": null,
                "native_helper_interpreter_confirmation_count": null,
                "native_helper_missing_var_fallback_count": null,
                "native_helper_trusted_true_count": null,
                "native_install_count": null,
                "par2": 18.0,
                "proof_failures": 0,
                "solved": 4,
                "witness_failures": 0,
                "wrong_answers": 1
            },
            "candidate_mode": "current",
            "failures": [],
            "native_dispatch": true,
            "recommended_mode": "current",
            "status": "pass",
            "track": "sat"
        }
    });

    let report_path = tmp.path().join("sat-stale-source-and-hash.json");
    write_file(
        &report_path,
        &serde_json::to_string_pretty(&report).expect("serialize release report"),
    );
    report_path
}

#[test]
fn competition_jit_matrix_check_succeeds() {
    let output = run_ay(&["competition-jit", "matrix", "check", "--json"]);
    assert_success(&output, "competition-jit matrix check");

    let payload = stdout_json(&output);
    assert_eq!(payload["status"], "pass", "{payload}");
    assert_eq!(
        payload["matrix"], "competition/jit_mode_matrix.json",
        "{payload}"
    );
    assert_eq!(
        payload["matrix_schema"], "competition/jit_mode_matrix.schema.json",
        "{payload}"
    );

    let modes = payload["modes"].as_array().expect("modes must be an array");
    for mode in ["off", "current", "solver-program", "profile-only"] {
        assert!(
            modes.iter().any(|value| value == mode),
            "missing mode {mode}: {payload}"
        );
    }

    let tracks = payload["tracks"]
        .as_array()
        .expect("tracks must be an array");
    for track in ["sat", "smt", "pb", "chc"] {
        assert!(
            tracks.iter().any(|value| value == track),
            "missing track {track}: {payload}"
        );
    }
}

#[test]
fn competition_jit_hot_inputs_emits_known_packet() {
    let output = run_ay(&["competition-jit", "hot-inputs", "--json"]);
    assert_success(&output, "competition-jit hot-inputs");

    let packet = stdout_json(&output);
    assert_eq!(packet["schema"], "ay.jit-roi-hot-inputs/v1", "{packet}");
    assert_eq!(packet["issue"], 9088, "{packet}");
    assert_eq!(packet["settings"]["fail_on_gate_fail"], true, "{packet}");

    let commands = packet["commands"]
        .as_array()
        .expect("commands must be an array");
    let artifacts: Vec<&str> = commands
        .iter()
        .map(|entry| {
            entry["artifact"]
                .as_str()
                .expect("artifact must be a string")
        })
        .collect();

    for artifact in [
        "smt-lra-sparse-substitute",
        "smt-lra-basis-regions",
        "pb-native-code-helpers",
    ] {
        assert!(
            artifacts.contains(&artifact),
            "missing {artifact}: {packet}"
        );
    }
    for entry in commands {
        let argv = entry["argv"].as_array().expect("argv must be an array");
        let legacy_probe = ["scripts", &["jit_roi", "_probe.py"].concat()].join("/");
        assert_eq!(argv[0], "ay", "{entry}");
        assert_eq!(argv[1], "competition-jit", "{entry}");
        assert_eq!(argv[2], "probe", "{entry}");
        assert!(
            !entry.to_string().contains(&legacy_probe),
            "hot-input packet must not reference the deleted Python probe helper: {entry}"
        );
        assert!(
            !argv.iter().any(|value| value == "py"),
            "legacy --python value must not be present in product argv: {entry}"
        );
    }

    let sparse = commands
        .iter()
        .find(|entry| entry["artifact"] == "smt-lra-sparse-substitute")
        .expect("sparse substitute packet entry");
    assert_eq!(
        sparse["application_counter"], "lra_external_codegen_backend_substitute_native_applies",
        "{sparse}"
    );
    assert_eq!(sparse["candidate_mode"], "profile-only", "{sparse}");
    assert_eq!(
        sparse["expected_counters"]["lra_external_codegen_backend_substitute_native_applies"],
        json!({"minimum": 1, "fixture_value": 3}),
        "{sparse}"
    );
    assert!(
        sparse["argv"]
            .as_array()
            .expect("argv must be an array")
            .iter()
            .any(|value| value == "--fail-on-gate-fail"),
        "hot-input packet should preserve fail-on-gate-fail argv: {sparse}"
    );

    let pb = commands
        .iter()
        .find(|entry| entry["artifact"] == "pb-native-code-helpers")
        .expect("PB native helper packet entry");
    assert_eq!(
        pb["application_counter"], "pb_native_code_helper_applications",
        "{pb}"
    );
    assert!(
        pb["argv"]
            .as_array()
            .expect("argv must be an array")
            .iter()
            .any(|value| value == "--pb-native"),
        "PB packet should preserve --pb-native probe argv: {pb}"
    );
}

#[test]
fn competition_jit_hot_inputs_shell_output_filters_to_product_probe() {
    let tmp = TempDir::new().expect("create temp dir");
    let ay_bin = tmp.path().join("ay-product");
    let report_dir = tmp.path().join("jit-hot");
    let output = run_ay(&[
        "competition-jit",
        "hot-inputs",
        "--artifact",
        "smt-lra-basis-regions",
        "--ay",
        ay_bin.to_str().expect("ay path must be utf-8"),
        "--report-dir",
        report_dir.to_str().expect("report dir must be utf-8"),
        "--timeout-ms",
        "250",
        "--no-fail-on-gate-fail",
    ]);
    assert_success(&output, "competition-jit hot-inputs shell");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let commands = stdout
        .lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .collect::<Vec<_>>();
    assert_eq!(commands.len(), 1, "{stdout}");
    let command = commands[0];
    assert!(
        command.contains("competition-jit probe --track smt --artifact smt-lra-basis-regions"),
        "{stdout}"
    );
    assert!(command.contains(ay_bin.to_str().unwrap()), "{stdout}");
    assert!(command.contains("--timeout-ms 250"), "{stdout}");
    assert!(command.contains(report_dir.to_str().unwrap()), "{stdout}");
    assert!(!command.contains("--fail-on-gate-fail"), "{stdout}");
    let legacy_probe = ["scripts", &["jit_roi", "_probe.py"].concat()].join("/");
    assert!(!stdout.contains(&legacy_probe), "{stdout}");
}

#[test]
fn competition_jit_gate_accepts_baseline_candidate_summaries() {
    let tmp = TempDir::new().expect("create temp dir");
    let baseline = tmp.path().join("baseline.json");
    let candidate = tmp.path().join("candidate.json");
    write_json_file(
        &baseline,
        &json!({
            "solved": 4,
            "par2": 20.0,
            "sat_learned_clause_candidate_applications": 0
        }),
    );
    write_json_file(
        &candidate,
        &json!({
            "schema": "ay.stats-json/v1",
            "competition_jit": {
                "schema_version": 1,
                "track": "sat",
                "artifact": "sat-learned-clause-candidates",
                "candidate_mode": "profile-only",
                "application_counter": "sat_learned_clause_candidate_applications"
            },
            "solved": 4,
            "par2": 18.0,
            "sat_learned_clause_candidate_applications": 2
        }),
    );

    let output = run_ay(&[
        "competition-jit",
        "gate",
        "--track",
        "sat",
        "--artifact",
        "sat-learned-clause-candidates",
        "--candidate-mode",
        "profile-only",
        "--baseline",
        baseline.to_str().expect("baseline path must be utf-8"),
        "--candidate",
        candidate.to_str().expect("candidate path must be utf-8"),
        "--require-summary-metadata",
        "--json",
    ]);
    assert_success(&output, "competition-jit gate baseline/candidate");

    let decision = stdout_json(&output);
    assert_eq!(decision["status"], "pass", "{decision}");
    assert_eq!(decision["recommended_mode"], "profile-only", "{decision}");
    assert_eq!(decision["native_dispatch"], false, "{decision}");
    assert_eq!(decision["candidate"]["application_count"], 2, "{decision}");
}

#[test]
fn competition_jit_release_validate_rejects_stale_source_hash_and_forged_gate() {
    let tmp = TempDir::new().expect("create temp dir");
    let report = stale_release_report(&tmp);

    let output = run_ay(&[
        "competition-jit",
        "release",
        "validate",
        "--report",
        report.to_str().expect("release report path must be utf-8"),
        "--json",
    ]);

    assert!(
        !output.status.success(),
        "stale release report should fail validation\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let combined = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("source.source_tree_sha256"),
        "expected stale source-tree diagnostic, got:\n{combined}"
    );
    assert!(
        combined.contains("package.artifact_sha256 must match"),
        "expected stale package artifact hash diagnostic, got:\n{combined}"
    );
    assert!(
        combined.contains("gate.recommended_mode must match recomputed value")
            || combined.contains("gate.failures must match recomputed"),
        "expected recomputed gate mismatch diagnostic, got:\n{combined}"
    );
}

#[test]
fn competition_jit_probe_dry_run_does_not_require_binary() {
    let tmp = TempDir::new().expect("create temp dir");
    let probe = tmp.path().join("case_sat.opb");
    write_file(&probe, "* #variable=1 #constraint=1\n1 x1 >= 1;\n");
    let missing_ay = tmp.path().join("does-not-exist");

    let output = run_ay(&[
        "competition-jit",
        "probe",
        "--track",
        "pb",
        "--artifact",
        "pb-native-code-helpers",
        "--ay",
        missing_ay.to_str().expect("missing ay path must be utf-8"),
        "--probe",
        probe.to_str().expect("probe path must be utf-8"),
        "--dry-run",
        "--json",
    ]);
    assert_success(&output, "competition-jit probe dry-run");

    let report = stdout_json(&output);
    assert_eq!(report["status"], "dry-run", "{report}");
    assert_eq!(report["gate"], Value::Null, "{report}");

    let runs = report["runs"].as_array().expect("runs must be an array");
    assert!(
        !runs.is_empty(),
        "dry-run should report planned runs: {report}"
    );
    assert!(
        runs.iter().all(|run| run["status"] == "dry-run"),
        "all planned probe runs should be dry-run rows: {report}"
    );
}

#[test]
fn competition_jit_probe_executes_fake_ay_and_writes_report() {
    let tmp = TempDir::new().expect("create temp dir");
    let fake_ay = tmp.path().join("fake-ay");
    write_file(
        &fake_ay,
        r#"#!/usr/bin/env sh
app=0
if [ "${AY_COMPETITION_JIT_MODE:-}" = "profile-only" ]; then
  app=2
fi
printf 'sat\n'
printf '{"schema":"ay.stats-json/v1","result":"sat","elapsed_sec":0.01,"counters":{"lra_external_codegen_backend_substitute_native_applies":%s,"lra_external_codegen_backend_substitute_wrapper_applies":%s},"totals":{"solved":1,"par2":0.01,"wrong_answers":0,"proof_failures":0,"witness_failures":0,"crashes":0}}\n' "$app" "$app" >&2
"#,
    );
    make_executable(&fake_ay);
    let probe = tmp.path().join("case.smt2");
    write_file(&probe, "(set-logic QF_LRA)\n(check-sat)\n");
    let missing = tmp.path().join("missing.smt2");
    let report_path = tmp.path().join("probe-report.json");

    let output = run_ay(&[
        "competition-jit",
        "probe",
        "--track",
        "smt",
        "--artifact",
        "smt-lra-sparse-substitute",
        "--candidate-mode",
        "profile-only",
        "--ay",
        fake_ay.to_str().expect("fake ay path must be utf-8"),
        "--probe",
        probe.to_str().expect("probe path must be utf-8"),
        "--probe",
        missing.to_str().expect("missing path must be utf-8"),
        "--out",
        report_path.to_str().expect("report path must be utf-8"),
        "--json",
        "--fail-on-gate-fail",
    ]);
    assert_success(&output, "competition-jit probe fake ay");

    let report = stdout_json(&output);
    assert_eq!(report["status"], "pass", "{report}");
    assert_eq!(report["gate"]["status"], "pass", "{report}");
    assert_eq!(
        report["comparison"]["gate_inputs"]["artifact_id"], "smt-lra-sparse-substitute",
        "{report}"
    );
    assert_eq!(
        report["summaries"]["candidate"]["counters"]
            ["lra_external_codegen_backend_substitute_native_applies"],
        2,
        "{report}"
    );
    assert_eq!(report["settings"]["skipped_runs"], 2, "{report}");
    assert!(
        report["evidence_failures"]
            .as_array()
            .expect("evidence_failures must be an array")
            .is_empty(),
        "{report}"
    );
    assert!(report_path.is_file(), "probe report should be written");
}

#[test]
fn competition_jit_probe_fail_on_gate_fail_rejects_missing_stats_json() {
    let tmp = TempDir::new().expect("create temp dir");
    let fake_ay = tmp.path().join("fake-ay-no-stats");
    write_file(&fake_ay, "#!/usr/bin/env sh\nprintf 'sat\\n'\n");
    make_executable(&fake_ay);
    let probe = tmp.path().join("case.smt2");
    write_file(&probe, "(set-logic QF_LRA)\n(check-sat)\n");

    let output = run_ay(&[
        "competition-jit",
        "probe",
        "--track",
        "smt",
        "--artifact",
        "smt-lra-sparse-substitute",
        "--candidate-mode",
        "profile-only",
        "--ay",
        fake_ay.to_str().expect("fake ay path must be utf-8"),
        "--probe",
        probe.to_str().expect("probe path must be utf-8"),
        "--json",
        "--fail-on-gate-fail",
    ]);
    assert!(
        !output.status.success(),
        "missing stats JSON should fail with --fail-on-gate-fail\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let report = stdout_json(&output);
    assert_eq!(report["status"], "fail", "{report}");
    let failures = report["evidence_failures"]
        .as_array()
        .expect("evidence_failures must be an array");
    assert!(
        failures
            .iter()
            .any(|failure| failure["kind"] == "missing-stats-json"),
        "{report}"
    );
}
