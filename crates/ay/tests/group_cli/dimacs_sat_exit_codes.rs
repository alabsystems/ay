// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIMACS verdict exit codes: SAT-Competition 10/20 vs Z3's 0.
//!
//! The SAT Competition reserves exit 10 for SATISFIABLE and 20 for
//! UNSATISFIABLE. Z3 uses neither -- it exits 0 for both and reports the
//! verdict on stdout alone. A drop-in `z3` install must follow Z3, or every
//! caller that tests `$?` reads the verdict as a failure.
//!
//! Both conventions are asserted here against the *same* binary, so neither
//! test can pass by the code hardcoding one answer.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

const SAT_CNF: &str = "p cnf 2 2\n1 2 0\n-1 0\n";
const UNSAT_CNF: &str = "p cnf 1 2\n1 0\n-1 0\n";

/// A scratch directory holding `sat.cnf` and `unsat.cnf`.
fn scratch() -> (PathBuf, DirGuard) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "ay_sat_exit_codes_{}_{}",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("sat.cnf"), SAT_CNF).unwrap();
    std::fs::write(dir.join("unsat.cnf"), UNSAT_CNF).unwrap();
    (dir.clone(), DirGuard(dir))
}

/// Run `program` (an AY image, possibly installed under another name) on the
/// named CNF and return `(exit code, stdout)`.
fn solve(program: &Path, dir: &Path, cnf: &str, args: &[&str]) -> (i32, String) {
    let output = Command::new(program)
        .args(args)
        .arg(dir.join(cnf))
        .output()
        .unwrap_or_else(|e| panic!("failed to run {}: {e}", program.display()));
    let code = output
        .status
        .code()
        .unwrap_or_else(|| panic!("{} died on a signal", program.display()));
    (code, String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Copy the AY binary into `dir` under `name`, mimicking a drop-in install.
/// A copy, not a symlink: the copy is what a package manager actually ships,
/// and it also pins the image under test rather than tracking `target/`.
fn install_as(dir: &Path, name: &str) -> PathBuf {
    let dest = dir.join(name);
    std::fs::copy(env!("CARGO_BIN_EXE_ay"), &dest).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&dest, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    dest
}

/// Invoked under its own name, AY keeps the competition codes. This is the
/// control: it fails if the Z3 convention is ever applied unconditionally.
#[test]
fn dimacs_under_ay_name_keeps_competition_exit_codes() {
    let (dir, _guard) = scratch();
    let ay = PathBuf::from(env!("CARGO_BIN_EXE_ay"));

    let (sat, _) = solve(&ay, &dir, "sat.cnf", &[]);
    assert_eq!(sat, 10, "SAT under the `ay` name must keep exit 10");

    let (unsat, _) = solve(&ay, &dir, "unsat.cnf", &[]);
    assert_eq!(unsat, 20, "UNSAT under the `ay` name must keep exit 20");
}

/// Installed as `z3`, AY must exit 0 for both verdicts, as Z3 does.
#[test]
fn dimacs_drop_in_z3_install_uses_z3_exit_codes() {
    let (dir, _guard) = scratch();
    let z3 = install_as(&dir, "z3");

    let (sat, _) = solve(&z3, &dir, "sat.cnf", &[]);
    assert_eq!(sat, 0, "a drop-in `z3` must exit 0 on SAT, as Z3 does");

    let (unsat, _) = solve(&z3, &dir, "unsat.cnf", &[]);
    assert_eq!(unsat, 0, "a drop-in `z3` must exit 0 on UNSAT, as Z3 does");
}

/// `--z3-mode` selects the Z3 convention without renaming the binary.
#[test]
fn dimacs_z3_mode_flag_uses_z3_exit_codes() {
    let (dir, _guard) = scratch();
    let ay = PathBuf::from(env!("CARGO_BIN_EXE_ay"));

    assert_eq!(solve(&ay, &dir, "sat.cnf", &["--z3-mode"]).0, 0);
    assert_eq!(solve(&ay, &dir, "unsat.cnf", &["--z3-mode"]).0, 0);
}

/// `--sat-exit-codes` overrides whichever default the invocation implies --
/// in both directions.
#[test]
fn sat_exit_codes_flag_overrides_both_defaults() {
    let (dir, _guard) = scratch();
    let ay = PathBuf::from(env!("CARGO_BIN_EXE_ay"));
    let z3 = install_as(&dir, "z3");

    // Forced onto the competition codes despite the `z3` name.
    let forced = ["--sat-exit-codes", "competition"];
    assert_eq!(solve(&z3, &dir, "sat.cnf", &forced).0, 10);
    assert_eq!(solve(&z3, &dir, "unsat.cnf", &forced).0, 20);

    // Forced onto the Z3 codes despite the `ay` name.
    let forced = ["--sat-exit-codes", "z3"];
    assert_eq!(solve(&ay, &dir, "sat.cnf", &forced).0, 0);
    assert_eq!(solve(&ay, &dir, "unsat.cnf", &forced).0, 0);
}

/// A competition harness signal must not be weakened by this change: the
/// exit codes stay 10/20 for an unrenamed binary. Guards the wrapper token
/// the shipped submission script actually composes (`...-drat-v1`), which is
/// absent from `SAT_COMPETITION_WRAPPER_TOKENS`.
#[test]
fn competition_env_signals_keep_competition_exit_codes() {
    let (dir, _guard) = scratch();
    let ay = PathBuf::from(env!("CARGO_BIN_EXE_ay"));

    for (key, value) in [
        (
            "AY_INTERNAL_SATCOMP_WRAPPER",
            "main-regular-default-drat-v1",
        ),
        ("AY_SAT_PROFILE_ID", "any"),
    ] {
        let out = Command::new(&ay)
            .env(key, value)
            .arg(dir.join("unsat.cnf"))
            .output()
            .unwrap();
        assert_eq!(
            out.status.code(),
            Some(20),
            "competition signal {key}={value} must keep exit 20"
        );
    }
}

/// The exit-code convention changes only the code. Stdout -- the verdict line
/// and any `v` model line -- is identical either way.
#[test]
fn exit_code_convention_does_not_change_stdout() {
    let (dir, _guard) = scratch();
    let ay = PathBuf::from(env!("CARGO_BIN_EXE_ay"));
    let z3 = install_as(&dir, "z3");

    for cnf in ["sat.cnf", "unsat.cnf"] {
        let (native_code, native_out) = solve(&ay, &dir, cnf, &[]);
        let (z3_code, z3_out) = solve(&z3, &dir, cnf, &[]);
        assert_ne!(native_code, z3_code, "{cnf}: the codes must differ");
        assert_eq!(native_out, z3_out, "{cnf}: stdout must be identical");
    }
}
