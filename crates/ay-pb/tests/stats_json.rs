// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_opb(contents: &str) -> (PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_pb_stats_json_{}_{}.opb",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp OPB fixture");
    (path.clone(), CleanupGuard(path))
}

#[test]
fn standalone_pb_stats_json_uses_shared_metadata_shape() {
    let ay_path = env!("CARGO_BIN_EXE_ay-pb");
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
        .arg(&temp_path)
        .env_remove("AY_COMPETITION_JIT_MODE")
        // Pin the SEQUENTIAL portfolio: this test asserts the sequential
        // path's per-phase `pb_portfolio_*_ms` stats schema, which the
        // parallel track (now the multi-core default) deliberately omits
        // (`portfolio_timings: None`, as it always has when enabled).
        .env("AY_PB_PARALLEL", "0")
        .output()
        .expect("spawn standalone ay-pb binary");

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

    let stderr = String::from_utf8_lossy(&output.stderr);
    let json_lines: Vec<&str> = stderr
        .lines()
        .filter(|line| line.trim_start().starts_with('{'))
        .collect();
    assert_eq!(
        json_lines.len(),
        1,
        "expected one stats JSON line on stderr, got: {stderr}"
    );
    let json_line = json_lines[0];

    for expected in [
        "\"mode\":\"pb\"",
        "\"result\":\"sat\"",
        "\"wall_time_ms\":",
        "\"ay_build\":{",
        "\"version\":",
        "\"commit\":",
        "\"datetime_utc\":",
        "\"stamp\":",
        "\"competition_jit\":{",
        "\"schema_version\":1",
        "\"track\":\"pb\"",
        "\"artifact\":\"pb-pbo-candidates\"",
        "\"application_counter\":\"pb_pbo_candidate_applications\"",
        "\"requested_mode\":\"profile-only\"",
        "\"candidate_mode\":\"profile-only\"",
        "\"native_dispatch\":false",
        "\"fail_closed\":false",
        "\"pb_pbo_candidate_applications\":4",
        "\"pb_portfolio_total_ms\":",
        "\"pb_portfolio_profile_ms\":",
        "\"pb_portfolio_max_clique_ms\":",
        "\"pb_portfolio_root_unsat_precheck_ms\":",
        "\"pb_portfolio_pre_native_sat_ms\":",
        "\"pb_portfolio_prefix_incumbent_ms\":",
        "\"pb_portfolio_native_ms\":",
        "\"pb_portfolio_sat_ms\":",
        "\"pb_clique_published_exact_continue\":",
        "\"pb_clique_published_exact_decision\":",
        "\"pb_clique_published_exact_exchange\":",
    ] {
        assert!(
            json_line.contains(expected),
            "expected stats JSON to contain {expected}: {json_line}"
        );
    }
    assert_eq!(
        pb_native_helper_applications(json_line),
        0,
        "profile-only standalone solve should not report solve-path native-helper applications: {json_line}"
    );
    assert!(
        !json_line.contains("\"elapsed_ms\""),
        "standalone stats JSON should use shared wall_time_ms key: {json_line}"
    );
}

#[test]
fn standalone_pb_stats_json_current_mode_reports_candidate_fail_closed() {
    let ay_path = env!("CARGO_BIN_EXE_ay-pb");
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
        // Pin the sequential route so the assertions below are deterministic
        // regardless of the host's parallel default.
        .env("AY_PB_PARALLEL", "0")
        .output()
        .expect("spawn standalone ay-pb binary");

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected PB SAT exit code 10; stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("pb_native_code_helper_applications"),
        "stats JSON must stay on stderr, stdout was: {stdout}"
    );

    let stderr = String::from_utf8_lossy(&output.stderr);
    let json_lines: Vec<&str> = stderr
        .lines()
        .filter(|line| line.trim_start().starts_with('{'))
        .collect();
    assert_eq!(
        json_lines.len(),
        1,
        "expected one stats JSON line on stderr, got: {stderr}"
    );
    let json_line = json_lines[0];

    let (expected_artifact, expected_counter) = {
        (
            "\"artifact\":\"pb-pbo-candidates\"",
            "\"application_counter\":\"pb_pbo_candidate_applications\"",
        )
    };

    for expected in [
        expected_artifact,
        expected_counter,
        "\"requested_mode\":\"current\"",
        "\"candidate_mode\":\"off\"",
        "\"native_dispatch\":false",
        "\"fail_closed\":true",
        "\"pb_pbo_candidate_applications\":4",
    ] {
        assert!(
            json_line.contains(expected),
            "expected stats JSON to contain {expected}: {json_line}"
        );
    }
    let applications = pb_native_helper_applications(json_line);
    {
        assert_eq!(
            applications, 0,
            "default standalone ay-pb should not report root solve-path native-helper applications: {json_line}"
        );
    }
}

/// Companion to `standalone_pb_stats_json_uses_shared_metadata_shape`: the
/// PARALLEL route's stats envelope is a pinned contract too. `AY_PB_PARALLEL=4`
/// forces the parallel portfolio deterministically (regardless of the host's
/// default), and the same decision fixture must produce the shared envelope
/// (`mode`/`result`/`wall_time_ms`/`ay_build`) on exactly one stderr JSON line —
/// while DELIBERATELY omitting the sequential portfolio's phase timings
/// (`pb_portfolio_*`) and clique-witness counters (`pb_clique_published_*`),
/// which do not exist on the parallel route.
#[test]
fn standalone_pb_stats_json_parallel_route_keeps_shared_envelope() {
    let ay_path = env!("CARGO_BIN_EXE_ay-pb");
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
        .arg(&temp_path)
        .env_remove("AY_COMPETITION_JIT_MODE")
        // Deterministically parallel with a fixed worker count, regardless of
        // the host's default or core count.
        .env("AY_PB_PARALLEL", "4")
        .output()
        .expect("spawn standalone ay-pb binary");

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

    let stderr = String::from_utf8_lossy(&output.stderr);
    let json_lines: Vec<&str> = stderr
        .lines()
        .filter(|line| line.trim_start().starts_with('{'))
        .collect();
    assert_eq!(
        json_lines.len(),
        1,
        "expected one stats JSON line on stderr, got: {stderr}"
    );
    let json_line = json_lines[0];

    for expected in [
        "\"mode\":\"pb\"",
        "\"result\":\"sat\"",
        "\"wall_time_ms\":",
        "\"ay_build\":{",
    ] {
        assert!(
            json_line.contains(expected),
            "expected parallel-route stats JSON to contain {expected}: {json_line}"
        );
    }
    // The omission IS the contract: no key with these prefixes may appear on
    // the parallel route (the sequential-only sections above).
    for forbidden_prefix in ["\"pb_portfolio_", "\"pb_clique_published_"] {
        assert!(
            !json_line.contains(forbidden_prefix),
            "parallel-route stats JSON must omit {forbidden_prefix}*\" keys: {json_line}"
        );
    }
}

fn pb_native_helper_applications(json_line: &str) -> u64 {
    let marker = "\"pb_native_code_helper_applications\":";
    json_line
        .split(marker)
        .nth(1)
        .and_then(|suffix| suffix.split(['}', ',']).next())
        .and_then(|value| value.parse::<u64>().ok())
        .expect("PB native-helper applications should be numeric")
}
