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
        // The oracle is resolved from PATH alone here; an ambient Z3_PATH
        // would bypass the hermetic PATH each test builds.
        .env_remove("Z3_PATH")
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

/// A fake z3 that proves its identity the way real z3 does (a `Z3 version`
/// banner for `--version`, an error for `--z3-mode`) and then answers
/// `answer` with `exit_code`.
#[cfg(unix)]
fn install_fake_z3(directory: &TestDirectory, answer: &str, exit_code: u8) {
    install_z3_script(
        directory,
        &format!(
            "#!/bin/sh\ncase \"$1\" in\n  --version) printf 'Z3 version 4.16.0 - 64 bit\\n'; exit 0;;\n  \
             --z3-mode) printf 'Error: invalid command line option: --z3-mode\\n'; exit 109;;\n\
             esac\n/bin/cat >/dev/null\nprintf '{answer}\\n'\nexit {exit_code}\n"
        ),
    );
}

#[cfg(unix)]
fn install_z3_script(directory: &TestDirectory, script: &str) {
    use std::os::unix::fs::PermissionsExt;

    let z3 = directory.path.join("z3");
    fs::write(&z3, script).expect("write fake z3");
    let mut permissions = fs::metadata(&z3).expect("stat fake z3").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(z3, permissions).expect("make fake z3 executable");
}

/// A program named `z3` that answers `unsat` to everything but never proves
/// it is z3 must not confirm an optimum, and neither may an AY drop-in that
/// prints z3's banner under `--z3-mode`.
#[cfg(unix)]
#[test]
fn a_z3_that_does_not_prove_its_identity_cannot_confirm_an_optimum() {
    let directory = TestDirectory::new();
    let instance = directory.write("instance.opb", INSTANCE);
    let solution = "o 2\ns OPTIMUM FOUND\nv x1 x2 -x3\n";
    for (name, script) in [
        (
            "no-banner",
            "#!/bin/sh\n/bin/cat >/dev/null\nprintf 'unsat\\n'\nexit 0\n",
        ),
        (
            "impostor",
            "#!/bin/sh\ncase \"$1\" in\n  --version|--z3-mode) printf 'Z3 version 5.1.0 - 64 bit\\n'; exit 0;;\n\
             esac\n/bin/cat >/dev/null\nprintf 'unsat\\n'\nexit 0\n",
        ),
    ] {
        install_z3_script(&directory, script);
        let output = run_verify(
            &directory,
            &instance,
            &format!("{name}.out"),
            solution,
            &["--require-z3"],
            &directory.path,
        );
        assert_summary(&output, 1, "s VERIFICATION UNVERIFIED");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("no usable z3"),
            "{name}: {}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
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
