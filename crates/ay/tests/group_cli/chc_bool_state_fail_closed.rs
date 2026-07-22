// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(unix)]
use std::time::Instant;

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn ay_exe() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn write_temp_chc(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_chc_bool_state_fail_closed_{}_{}.smt2",
        std::process::id(),
        file_id
    ));
    fs::write(&path, contents).expect("write CHC input");
    (path.clone(), CleanupGuard(path))
}

#[test]
#[timeout(30_000)]
fn bool_state_horn_safe_certificate_emits_validated_sat() {
    let (input, _guard) = write_temp_chc(
        r#"(set-logic HORN)
(declare-fun State (Bool) Bool)
(assert (forall ((b Bool)) (=> (= b true) (State b))))
(assert (forall ((b Bool)) (=> (and (State b) (= b false)) false)))
(check-sat)
"#,
    );

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg("--timeout")
        .arg("1000")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "ay should fail closed without process failure: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        stdout.lines().next(),
        Some("sat"),
        "validated Bool-state non-fixedpoint CHC safe certificates should print sat: stdout={stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn malformed_chc_input_fails_closed_to_single_unknown() {
    let (input, _guard) = write_temp_chc(
        r#"(set-logic HORN)
(assert
"#,
    );

    let output = Command::new(ay_exe())
        .arg("--chc")
        .arg(&input)
        .output()
        .expect("spawn ay");

    assert!(
        output.status.success(),
        "CHC parse failures should fail closed at the CLI boundary: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "unknown\n",
        "CHC parse failures must emit exactly one unknown on stdout"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("CHC fail-closed"),
        "stderr should preserve the fail-closed diagnostic for operators"
    );
}

#[cfg(unix)]
#[test]
#[timeout(60_000)]
fn generated_chc_wrapper_filters_status_to_exactly_one_line() {
    let temp = tempfile::tempdir().expect("temp dir");
    let package = temp.path().join("chc-package");
    let package_output = Command::new(ay_exe())
        .args(["submission", "package", "chc", "--output"])
        .arg(&package)
        .args(["--ay-bin", ay_exe()])
        .output()
        .expect("package CHC submission");
    assert!(
        package_output.status.success(),
        "CHC package should generate; stdout={} stderr={}",
        String::from_utf8_lossy(&package_output.stdout),
        String::from_utf8_lossy(&package_output.stderr)
    );

    let wrapper = package.join("tool-archive/ay/run_solver.sh");
    let malformed = temp.path().join("malformed.smt2");
    let missing = temp.path().join("missing.smt2");
    fs::write(&malformed, "(set-logic HORN)\n(assert\n").expect("write malformed CHC");
    assert_wrapper_stdout(&wrapper, &[malformed.as_path()], "unknown\n");
    assert_wrapper_stdout(&wrapper, &[missing.as_path()], "unknown\n");

    let fake_ay = package.join("tool-archive/ay/ay");
    fs::write(
        &fake_ay,
        "#!/usr/bin/env bash\nprintf '%s\\n' 'solver banner' sat unknown\n",
    )
    .expect("write first-status fake solver");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755)).expect("chmod fake solver");
    assert_wrapper_stdout(&wrapper, &[malformed.as_path()], "sat\n");

    fs::write(
        &fake_ay,
        "#!/usr/bin/env bash\nprintf '%s\\n' 'solver banner' '(model without status)'\n",
    )
    .expect("write no-status fake solver");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755)).expect("chmod fake solver");
    assert_wrapper_stdout(&wrapper, &[malformed.as_path()], "unknown\n");
}

#[cfg(unix)]
#[test]
#[timeout(60_000)]
fn generated_chc_wrapper_forwards_internal_timeout_to_solver() {
    let temp = tempfile::tempdir().expect("temp dir");
    let package = temp.path().join("chc-package");
    let package_output = Command::new(ay_exe())
        .args(["submission", "package", "chc", "--output"])
        .arg(&package)
        .args(["--ay-bin", ay_exe()])
        .output()
        .expect("package CHC submission");
    assert!(
        package_output.status.success(),
        "CHC package should generate; stdout={} stderr={}",
        String::from_utf8_lossy(&package_output.stdout),
        String::from_utf8_lossy(&package_output.stderr)
    );

    let input = temp.path().join("input.smt2");
    let args_file = temp.path().join("fake-ay-args.txt");
    fs::write(&input, "(set-logic HORN)\n(check-sat)\n").expect("write CHC input");

    let fake_ay = package.join("tool-archive/ay/ay");
    fs::write(
        &fake_ay,
        "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$AY_FAKE_ARGS_FILE\"\nprintf 'unknown\\n'\n",
    )
    .expect("write fake solver");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755)).expect("chmod fake solver");

    let wrapper = package.join("tool-archive/ay/run_solver.sh");
    let output = Command::new(&wrapper)
        .args(["--ay-timeout-ms", "1234"])
        .arg(&input)
        .env("AY_FAKE_ARGS_FILE", &args_file)
        .output()
        .expect("run CHC wrapper with explicit timeout");
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout), "unknown\n");
    let args = fs::read_to_string(&args_file).expect("read fake solver args");
    assert_eq!(
        args,
        format!("--chc\n--timeout\n1234\n{}\n", input.display())
    );

    let output = Command::new(&wrapper)
        .arg(&input)
        .env("TIMELIMIT", "30")
        .env("AY_FAKE_ARGS_FILE", &args_file)
        .output()
        .expect("run CHC wrapper with competition timeout env");
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout), "unknown\n");
    let args = fs::read_to_string(&args_file).expect("read fake solver args");
    assert_eq!(
        args,
        format!("--chc\n--timeout\n25000\n{}\n", input.display())
    );

    fs::write(&fake_ay, "#!/usr/bin/env bash\nsleep 3\nprintf 'sat\\n'\n")
        .expect("write slow fake solver");
    fs::set_permissions(&fake_ay, fs::Permissions::from_mode(0o755))
        .expect("chmod slow fake solver");
    let start = Instant::now();
    let output = Command::new(&wrapper)
        .args(["--ay-timeout-ms", "1000"])
        .arg(&input)
        .output()
        .expect("run CHC wrapper with wrapper watchdog");
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stdout), "unknown\n");
    assert!(
        start.elapsed().as_millis() < 2500,
        "wrapper watchdog should return before slow solver prints sat"
    );
}

#[cfg(unix)]
fn assert_wrapper_stdout(
    wrapper: &std::path::Path,
    args: &[&std::path::Path],
    expected_stdout: &str,
) {
    let output = Command::new(wrapper)
        .args(args.iter().map(|arg| arg.as_os_str()))
        .output()
        .expect("run CHC wrapper");
    assert!(
        output.status.success(),
        "CHC wrapper should always exit successfully at the boundary: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        expected_stdout,
        "CHC wrapper must emit exactly one status line"
    );
}
