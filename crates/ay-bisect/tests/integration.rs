// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// The production resource-admission guard deliberately fails closed without
// Linux procfs. These success-path end-to-end tests therefore run only where
// their required process-table capability exists; Python policy tests retain
// explicit coverage of the unsupported-target refusal.
//
// The guard also refuses while ANY other Cargo build runs on the host
// (`plan --warn-concurrent-build`). That refusal is correct for a real bisect,
// but it made these tests a function of unrelated host activity: on a shared
// build host all three failed whenever another worker was compiling. Each test
// therefore runs `ay-bisect` from its temp dir, where `locate_planner` finds a
// shim first. The shim records its argv and runs the REAL planner with every
// argument except `--warn-concurrent-build`, and each test asserts that
// `ay-bisect` still asked for that refusal.
#![cfg(target_os = "linux")]

//! End-to-end integration tests for `ay-bisect`.
//!
//! We do NOT require the real `ay` binary to be present. Instead we build a
//! small shell script that simulates ay's stdout as a function of which
//! `--no-*` CLI flags were passed, then drive the `ay-bisect` binary against
//! that script.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use tempfile::TempDir;

fn ay_bisect_binary() -> PathBuf {
    // Cargo pre-builds this package's own bin before running its integration
    // tests and hands us the path via CARGO_BIN_EXE_<name>. Using it — instead
    // of spawning a nested `cargo build` — avoids a build-directory lock
    // deadlock when this test runs under a workspace-wide `cargo test` that
    // already holds the lock.
    PathBuf::from(env!("CARGO_BIN_EXE_ay-bisect"))
}

/// Write a shell script that emulates `ay`. The script returns `fail_verdict`
/// unless *every* flag in `required_flags` appears among its CLI arguments,
/// in which case it returns `pass_verdict`. This simulates a "bug" whose fix
/// requires disabling a specific set of features.
fn write_mock_ay(
    dir: &Path,
    required_flags: &[&str],
    pass_verdict: &str,
    fail_verdict: &str,
) -> PathBuf {
    let script = dir.join("mock_ay.sh");
    let mut body = String::new();
    body.push_str("#!/bin/sh\n");
    body.push_str("# Mock ay binary for ay-bisect integration tests.\n");
    body.push_str("if [ \"$1\" = \"--version\" ] || [ \"$1\" = \"-V\" ]; then\n");
    body.push_str("  cat <<'EOF'\n");
    body.push_str("mock-ay-build\n");
    body.push_str("build.version=0.0.0-mock\n");
    body.push_str("build.increment=mock-1\n");
    body.push_str("build.commit=mock-commit\n");
    body.push_str("build.datetime_utc=2026-04-21T00:00:00Z\n");
    body.push_str("build.stamp=mock-ay-build\n");
    body.push_str("EOF\n");
    body.push_str("  exit 0\n");
    body.push_str("fi\n");
    body.push_str(&format!("pass=\"{pass_verdict}\"\n"));
    body.push_str(&format!("fail=\"{fail_verdict}\"\n"));
    // Collect all args into a space-separated string we can grep.
    body.push_str("args=\" $* \"\n");
    body.push_str("ok=1\n");
    for flag in required_flags {
        body.push_str(&format!(
            "case \" $args \" in *\" {flag} \"*) : ;; *) ok=0 ;; esac\n"
        ));
    }
    body.push_str("if [ \"$ok\" = \"1\" ]; then echo \"$pass\"; else echo \"$fail\"; fi\n");

    {
        let mut f = fs::File::create(&script).expect("create script");
        f.write_all(body.as_bytes()).expect("write script");
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&script).expect("stat").permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&script, perms).expect("chmod");
    }
    script
}

/// Install the planner shim described at the top of this file in `dir`, and
/// return the path of the argv log it appends to.
fn install_planner_shim(dir: &Path) -> PathBuf {
    let real = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/_oom_guard.py")
        .canonicalize()
        .expect("the repository planner exists");
    let scripts = dir.join("scripts");
    fs::create_dir_all(&scripts).expect("create shim dir");
    let argv_log = dir.join("planner_argv.txt");
    let shim = format!(
        "import subprocess, sys\n\
         with open({log:?}, 'a') as fh:\n    fh.write(' '.join(sys.argv[1:]) + '\\n')\n\
         args = [a for a in sys.argv[1:] if a != '--warn-concurrent-build']\n\
         sys.exit(subprocess.call([sys.executable, {real:?}] + args))\n",
        log = argv_log.display().to_string(),
        real = real.display().to_string(),
    );
    fs::write(scripts.join("_oom_guard.py"), shim).expect("write planner shim");
    argv_log
}

/// `ay-bisect` must still ask the planner to refuse during a concurrent build;
/// the shim only keeps that refusal from depending on the host.
fn assert_requested_concurrent_build_refusal(argv_log: &Path) {
    let calls = fs::read_to_string(argv_log).expect("ay-bisect ran the planner shim");
    assert!(
        calls
            .lines()
            .any(|call| call.starts_with("plan ") && call.contains("--warn-concurrent-build")),
        "ay-bisect planned without --warn-concurrent-build; planner calls:\n{calls}"
    );
}

#[test]
fn test_bisect_finds_single_culprit_bve() {
    let tmp = TempDir::new().expect("tempdir");
    let mock = write_mock_ay(tmp.path(), &["--no-bve"], "sat", "unsat");

    let smt2 = tmp.path().join("bug.smt2");
    fs::write(&smt2, "(set-logic QF_LIA)(assert true)(check-sat)\n").expect("smt2");

    let argv_log = install_planner_shim(tmp.path());
    let bin = ay_bisect_binary();
    let out = Command::new(&bin)
        .current_dir(tmp.path())
        .args([
            "--expected",
            "sat",
            "--timeout",
            "10",
            "--jobs",
            "2",
            "--ay-binary",
        ])
        .arg(&mock)
        .arg(&smt2)
        .output()
        .expect("run ay-bisect");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "ay-bisect exited {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        out.status.code()
    );
    assert_requested_concurrent_build_refusal(&argv_log);
    assert!(
        stdout.contains("ay binary:"),
        "expected ay binary path in report:\n{stdout}"
    );
    assert!(
        stdout.contains("ay build:  mock-ay-build"),
        "expected ay build summary in report:\n{stdout}"
    );
    assert!(
        stdout.contains(&mock.display().to_string()),
        "expected explicit mock binary path in report:\n{stdout}"
    );
    assert!(
        stdout.contains("--no-bve"),
        "expected --no-bve in report:\n{stdout}"
    );
    assert!(
        stdout.contains("sat"),
        "expected subsystem label in report:\n{stdout}"
    );
}

#[test]
fn test_bisect_json_output() {
    let tmp = TempDir::new().expect("tempdir");
    let mock = write_mock_ay(tmp.path(), &["--no-vivify"], "unsat", "sat");
    let smt2 = tmp.path().join("bug.smt2");
    fs::write(&smt2, "(set-logic QF_LIA)(assert true)(check-sat)\n").expect("smt2");

    let argv_log = install_planner_shim(tmp.path());
    let bin = ay_bisect_binary();
    let out = Command::new(&bin)
        .current_dir(tmp.path())
        .args([
            "--expected",
            "unsat",
            "--timeout",
            "10",
            "--jobs",
            "2",
            "--json",
            "--ay-binary",
        ])
        .arg(&mock)
        .arg(&smt2)
        .output()
        .expect("run ay-bisect");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_requested_concurrent_build_refusal(&argv_log);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let flags = parsed
        .get("minimal_flags")
        .and_then(|v| v.as_array())
        .expect("minimal_flags array");
    let has = flags.iter().any(|v| v.as_str() == Some("--no-vivify"));
    assert!(has, "expected --no-vivify in JSON: {stdout}");
}

#[test]
fn test_bisect_baseline_already_correct() {
    let tmp = TempDir::new().expect("tempdir");
    // Mock that always says "sat" regardless of args → baseline matches
    // --expected sat immediately; bisect short-circuits with empty flag set.
    let mock = write_mock_ay(tmp.path(), &[], "sat", "unsat");
    let smt2 = tmp.path().join("bug.smt2");
    fs::write(&smt2, "(set-logic QF_LIA)(assert true)(check-sat)\n").expect("smt2");

    let argv_log = install_planner_shim(tmp.path());
    let bin = ay_bisect_binary();
    let out = Command::new(&bin)
        .current_dir(tmp.path())
        .args([
            "--expected",
            "sat",
            "--timeout",
            "5",
            "--jobs",
            "1",
            "--json",
            "--ay-binary",
        ])
        .arg(&mock)
        .arg(&smt2)
        .output()
        .expect("run ay-bisect");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_requested_concurrent_build_refusal(&argv_log);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(parsed["baseline_already_correct"], true, "stdout: {stdout}");
    assert_eq!(parsed["minimal_flags"].as_array().unwrap().len(), 0);
    assert_eq!(parsed["trials"].as_u64().unwrap(), 1);
}
