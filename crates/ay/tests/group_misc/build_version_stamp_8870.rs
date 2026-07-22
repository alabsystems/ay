// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build-version provenance contract tests (#8870).

use ntest::timeout;
use std::collections::BTreeMap;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_file(contents: &str, ext: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_build_version_stamp_{}_{}.{ext}",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp file");
    (path.clone(), CleanupGuard(path))
}

fn ay_command() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    // Session markers are suppressed when launched from Cargo so
    // the broader suite keeps its current stderr contracts. Opt back in here.
    command.env_remove("CARGO");
    command.env_remove("CARGO_TARGET_TMPDIR");
    command
}

fn parse_build_fields(output: &str) -> BTreeMap<String, String> {
    output
        .lines()
        .filter_map(|line| {
            let (key, value) = line.split_once('=')?;
            key.starts_with("build.")
                .then(|| (key.to_string(), value.trim().to_string()))
        })
        .collect()
}

fn parse_marker_fields(line: &str) -> BTreeMap<String, String> {
    line.split_whitespace()
        .filter_map(|token| token.split_once('='))
        .map(|(key, value)| (key.to_string(), value.to_string()))
        .collect()
}

fn clean_commit(value: &str) -> &str {
    value.strip_suffix("-dirty").unwrap_or(value)
}

fn is_full_hex_commit(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[test]
#[timeout(30_000)]
fn version_output_includes_structured_build_provenance() {
    let output = ay_command()
        .arg("--version")
        .output()
        .expect("spawn ay --version");

    assert!(
        output.status.success(),
        "expected exit 0, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let fields = parse_build_fields(&stdout);

    for key in [
        "build.version",
        "build.increment",
        "build.commit",
        "build.datetime_utc",
        "build.stamp",
    ] {
        assert!(
            fields.get(key).is_some_and(|value| !value.is_empty()),
            "missing {key} in --version output: {stdout}"
        );
    }

    let datetime = &fields["build.datetime_utc"];
    assert!(
        datetime.contains('T') && datetime.ends_with('Z'),
        "expected ISO-8601 UTC build datetime, got {datetime}"
    );

    let stamp = &fields["build.stamp"];
    let commit = &fields["build.commit"];
    assert!(
        is_full_hex_commit(clean_commit(commit)),
        "build.commit should carry a full 40-hex commit, optionally with -dirty suffix; got {commit:?} in {stdout}"
    );
    assert!(
        stamp.contains(&fields["build.version"]),
        "build.stamp should include build.version: {stdout}"
    );
    assert!(
        stamp.contains(&fields["build.increment"]),
        "build.stamp should include build.increment: {stdout}"
    );
    assert!(
        stamp.contains(&fields["build.commit"]),
        "build.stamp should include build.commit: {stdout}"
    );
    assert!(
        stamp.contains(datetime),
        "build.stamp should include build.datetime_utc: {stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn short_v_alias_routes_to_version_output() {
    let long_output = ay_command()
        .arg("--version")
        .output()
        .expect("spawn ay --version");
    let short_output = ay_command().arg("-v").output().expect("spawn ay -v");

    assert!(
        long_output.status.success() && short_output.status.success(),
        "--version status={:?}, -v status={:?}",
        long_output.status,
        short_output.status
    );

    let long_stdout = String::from_utf8_lossy(&long_output.stdout);
    let short_stdout = String::from_utf8_lossy(&short_output.stdout);

    assert_eq!(
        parse_build_fields(&long_stdout),
        parse_build_fields(&short_stdout),
        "-v should route to the same structured version output as --version"
    );
}

#[test]
#[timeout(30_000)]
fn solve_session_emits_matching_start_and_end_build_stamp() {
    let version_output = ay_command()
        .arg("--version")
        .output()
        .expect("spawn ay --version");
    let version_stdout = String::from_utf8_lossy(&version_output.stdout);
    let version_fields = parse_build_fields(&version_stdout);

    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 42))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_file(input, "smt2");

    let output = ay_command()
        .arg(&temp_path)
        .output()
        .expect("spawn ay solve session");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected exit 0; stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        stdout.lines().next().unwrap_or(""),
        "sat",
        "expected SAT result; stdout={stdout}; stderr={stderr}"
    );

    let start_line = stderr
        .lines()
        .find(|line| line.starts_with("c ay.session.start "))
        .expect("missing session start marker");
    let end_line = stderr
        .lines()
        .find(|line| line.starts_with("c ay.session.end "))
        .expect("missing session end marker");

    let start_fields = parse_marker_fields(start_line);
    let end_fields = parse_marker_fields(end_line);

    assert_eq!(
        start_fields.get("build.version").map(String::as_str),
        Some(version_fields["build.version"].as_str()),
        "session start marker should report the same build.version as --version"
    );
    assert_eq!(
        start_fields.get("build.increment").map(String::as_str),
        Some(version_fields["build.increment"].as_str()),
        "session start marker should report the same build.increment as --version"
    );
    assert_eq!(
        start_fields.get("build.commit").map(String::as_str),
        Some(version_fields["build.commit"].as_str()),
        "session start marker should report the same build.commit as --version"
    );
    assert_eq!(
        end_fields.get("build.increment").map(String::as_str),
        Some(version_fields["build.increment"].as_str()),
        "session end marker should report the same build.increment as --version"
    );
    assert_eq!(
        start_fields.get("build.datetime_utc").map(String::as_str),
        Some(version_fields["build.datetime_utc"].as_str()),
        "session start marker should report the same build.datetime_utc as --version"
    );
    assert_eq!(
        start_fields.get("build.stamp").map(String::as_str),
        Some(version_fields["build.stamp"].as_str()),
        "session start marker should report the same build.stamp as --version"
    );
    assert_eq!(
        end_fields.get("build.stamp").map(String::as_str),
        Some(version_fields["build.stamp"].as_str()),
        "session end marker should report the same build.stamp as --version"
    );
    assert_eq!(
        end_fields.get("exit.code").map(String::as_str),
        Some("0"),
        "session end marker should include the exit code: {stderr}"
    );
    assert!(
        end_fields
            .get("wall_time_ms")
            .is_some_and(|value| value.parse::<u128>().is_ok()),
        "session end marker should include numeric wall_time_ms: {stderr}"
    );
}

#[test]
#[timeout(30_000)]
fn stats_json_keeps_single_json_stderr_contract() {
    let input = r#"(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 7))
(check-sat)
"#;
    let (temp_path, _cleanup) = write_temp_file(input, "smt2");

    let output = ay_command()
        .arg("--stats-json")
        .arg(&temp_path)
        .output()
        .expect("spawn ay --stats-json");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected exit 0; stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        stdout.lines().next().unwrap_or(""),
        "sat",
        "expected SAT result; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stderr.contains("c ay.session.start "),
        "--stats-json stderr must not include session markers: {stderr}"
    );
    assert!(
        !stderr.contains("c ay.session.end "),
        "--stats-json stderr must not include session markers: {stderr}"
    );

    let lines: Vec<&str> = stderr
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    assert_eq!(
        lines.len(),
        1,
        "--stats-json stderr should stay a single non-empty line: {stderr}"
    );

    let parsed: serde_json::Value =
        serde_json::from_str(lines[0]).expect("stats-json output should be valid JSON");
    assert_eq!(
        parsed["result"],
        serde_json::Value::String("sat".to_string()),
        "stats-json should report the solver result"
    );
    assert!(
        parsed.get("ay_build").is_some(),
        "stats-json should still include build provenance: {stderr}"
    );
}
