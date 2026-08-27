// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end authority checks for `ay-pb pb verify`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const INSTANCE: &str = "\
* #variable= 3 #constraint= 1
min: +1 x1 +1 x2 +1 x3 ;
+1 x1 +1 x2 +1 x3 >= 2 ;
";

const OVERFLOWING_OBJECTIVE_INSTANCE: &str = "\
* #variable= 2 #constraint= 2
min: +170141183460469231731687303715884105727 x1 +1 x2 ;
+1 x1 >= 1 ;
+1 x2 >= 1 ;
";

const MINIMUM_OBJECTIVE_INSTANCE: &str = "\
* #variable= 2 #constraint= 2
min: -170141183460469231731687303715884105727 x1 -1 x2 ;
+1 x1 >= 1 ;
+1 x2 >= 1 ;
";

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestDirectory {
    path: PathBuf,
}

impl TestDirectory {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ay-pb-verify-cli-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&path).expect("create verifier test directory");
        Self { path }
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path.join(name);
        fs::write(&path, contents).expect("write verifier test input");
        path
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn run_verify(
    directory: &TestDirectory,
    instance: &Path,
    name: &str,
    solution: &str,
    mode_args: &[&str],
    path: &Path,
) -> Output {
    let solution_path = directory.write(name, solution);
    Command::new(env!("CARGO_BIN_EXE_ay-pb"))
        .args(["pb", "verify"])
        .args(mode_args)
        .arg(instance)
        .arg(solution_path)
        .env("PATH", path)
        .output()
        .expect("run ay-pb verifier")
}

fn assert_summary(output: &Output, expected_code: i32, expected_summary: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        output.status.code(),
        Some(expected_code),
        "stdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.lines().any(|line| line == expected_summary),
        "missing {expected_summary:?} in stdout: {stdout:?}"
    );
    if expected_code != 0 {
        assert!(
            !stdout.contains("VERIFIED PASS"),
            "nonzero verifier result must not claim VERIFIED PASS: {stdout:?}"
        );
    }
}

#[test]
fn cli_distinguishes_verified_unverified_and_rejected_claims() {
    let directory = TestDirectory::new();
    let instance = directory.write("instance.opb", INSTANCE);
    let path_without_z3 = directory.path.join("empty-path");
    fs::create_dir_all(&path_without_z3).expect("create empty PATH directory");

    let verified_sat = run_verify(
        &directory,
        &instance,
        "sat.out",
        "s SATISFIABLE\nv x1 x2 -x3\n",
        &["--no-z3"],
        &path_without_z3,
    );
    assert_summary(&verified_sat, 0, "s VERIFICATION VERIFIED");

    for (name, solution) in [
        ("empty.out", ""),
        ("unknown.out", "s UNKNOWN\n"),
        ("unsupported.out", "s MAYBE\n"),
        ("unsat.out", "s UNSATISFIABLE\n"),
        ("optimum-no-objective.out", "s OPTIMUM FOUND\nv x1 x2 -x3\n"),
        ("optimum-no-z3.out", "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n"),
    ] {
        let output = run_verify(
            &directory,
            &instance,
            name,
            solution,
            &["--no-z3"],
            &path_without_z3,
        );
        assert_summary(&output, 1, "s VERIFICATION UNVERIFIED");
    }

    let rejected = run_verify(
        &directory,
        &instance,
        "infeasible.out",
        "s SATISFIABLE\nv x1 -x2 -x3\n",
        &["--no-z3"],
        &path_without_z3,
    );
    assert_summary(&rejected, 1, "s VERIFICATION REJECTED");

    let overflow_instance = directory.write("overflow.opb", OVERFLOWING_OBJECTIVE_INSTANCE);
    let overflow = run_verify(
        &directory,
        &overflow_instance,
        "overflow.out",
        "o 170141183460469231731687303715884105727\ns OPTIMUM FOUND\nv x1 x2\n",
        &["--no-z3"],
        &path_without_z3,
    );
    assert_summary(&overflow, 1, "s VERIFICATION REJECTED");
    assert!(String::from_utf8_lossy(&overflow.stdout).contains("OBJECTIVE OVERFLOW"));
}

#[test]
fn default_auto_mode_is_unverified_when_z3_is_absent() {
    let directory = TestDirectory::new();
    let instance = directory.write("instance.opb", INSTANCE);
    let path_without_z3 = directory.path.join("empty-path");
    fs::create_dir_all(&path_without_z3).expect("create empty PATH directory");
    let output = run_verify(
        &directory,
        &instance,
        "optimum.out",
        "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n",
        &[],
        &path_without_z3,
    );
    assert_summary(&output, 1, "s VERIFICATION UNVERIFIED");
}

#[cfg(unix)]
fn install_fake_z3(directory: &TestDirectory, answer: &str, exit_code: u8) {
    use std::os::unix::fs::PermissionsExt;

    let z3 = directory.path.join("z3");
    let script =
        format!("#!/bin/sh\n/bin/cat >/dev/null\nprintf '{answer}\\n'\nexit {exit_code}\n");
    fs::write(&z3, script).expect("write fake z3");
    let mut permissions = fs::metadata(&z3).expect("stat fake z3").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(z3, permissions).expect("make fake z3 executable");
}

#[cfg(unix)]
#[test]
fn cli_optimum_authority_follows_independent_checker_result() {
    let directory = TestDirectory::new();
    let instance = directory.write("instance.opb", INSTANCE);
    let solution = "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n";

    for (answer, code, summary) in [
        ("unsat", 0, "s VERIFICATION VERIFIED"),
        ("sat", 1, "s VERIFICATION REJECTED"),
        ("unknown", 1, "s VERIFICATION UNVERIFIED"),
    ] {
        install_fake_z3(&directory, answer, 0);
        let output = run_verify(
            &directory,
            &instance,
            &format!("z3-{answer}.out"),
            solution,
            &["--require-z3"],
            &directory.path,
        );
        assert_summary(&output, code, summary);
    }

    install_fake_z3(&directory, "unsat", 0);
    let minimum_instance = directory.write("minimum.opb", MINIMUM_OBJECTIVE_INSTANCE);
    let minimum = run_verify(
        &directory,
        &minimum_instance,
        "minimum.out",
        "o -170141183460469231731687303715884105728\ns OPTIMUM FOUND\nv x1 x2\n",
        &["--require-z3"],
        &directory.path,
    );
    assert_summary(&minimum, 1, "s VERIFICATION UNVERIFIED");

    install_fake_z3(&directory, "unsat", 9);
    let failed_checker = run_verify(
        &directory,
        &instance,
        "failed-checker.out",
        solution,
        &["--require-z3"],
        &directory.path,
    );
    assert_summary(&failed_checker, 1, "s VERIFICATION UNVERIFIED");
    assert!(String::from_utf8_lossy(&failed_checker.stdout)
        .contains("z3 did not exit successfully: exit status 9"));
}
