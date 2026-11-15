// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The z3 oracle resolver must never accept AY as its own oracle.
//!
//! AY is a z3 drop-in: run under the name `z3` it prints z3's exact
//! `Z3 version ...` banner, so a banner check alone would let an AY install
//! answer for z3 and turn every AY-vs-z3 differential into AY-vs-AY
//! agreement. `ay_sys::z3_oracle` therefore also runs a negative control,
//! `--z3-mode --version`, that real z3 rejects and AY answers with the
//! banner. This pins that rule against the real `ay` binary.

use ay_sys::z3_oracle::{resolve_z3, Z3Unavailable};
use std::process::Command;

#[cfg(unix)]
#[test]
fn ay_installed_as_z3_prints_the_banner_and_is_refused_as_the_z3_oracle() {
    let directory = tempfile::tempdir().expect("temporary directory");
    let z3 = directory.path().join("z3");
    std::os::unix::fs::symlink(env!("CARGO_BIN_EXE_ay"), &z3).expect("link ay as z3");

    // The premise: under the name z3, AY passes a banner-only identity check.
    let version = Command::new(&z3)
        .arg("--version")
        .output()
        .expect("run ay as z3 --version");
    let stdout = String::from_utf8_lossy(&version.stdout);
    assert!(
        version.status.success() && stdout.starts_with("Z3 version "),
        "ay as z3 no longer prints the z3 banner; revisit the negative control: {stdout:?}"
    );

    // The rule: the negative control refuses it, found on PATH ...
    let path = std::env::join_paths([directory.path()]).expect("join PATH");
    let Err(Z3Unavailable::NotFound { passed_over }) = resolve_z3(None, Some(&path)) else {
        panic!("AY linked as z3 was accepted as the z3 oracle");
    };
    assert_eq!(passed_over.len(), 1, "{passed_over:?}");
    assert!(
        passed_over[0].reason.contains("AY drop-in"),
        "{passed_over:?}"
    );

    // ... and named by Z3_PATH, which never falls back to PATH.
    let named = resolve_z3(Some(z3.as_os_str()), Some(&path))
        .expect_err("AY named by Z3_PATH was accepted as the z3 oracle");
    assert!(named.is_misconfigured(), "{named:?}");
}
