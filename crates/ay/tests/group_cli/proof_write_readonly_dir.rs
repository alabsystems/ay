// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A default (opportunistic) Alethe proof-write failure must NOT change the
//! exit code once the verdict is already on stdout. Regression for the
//! read-only input-directory deployment blocker (nix store, docker RO mount,
//! CI cache, mounted corpus): AY used to print `unsat` and then `exit 1` when
//! it could not write `<input>.alethe` next to a read-only input, breaking
//! every such deployment. z3 exits 0. The verdict is unaffected by whether the
//! optional certificate could be written.

use ntest::timeout;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn default_proof_write_failure_keeps_exit_zero_on_readonly_dir() {
    let dir = std::env::temp_dir().join(format!("ay_ro_proof_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp dir");
    let file = dir.join("unsat.smt2");
    fs::write(
        &file,
        "(declare-const x Int)\n(assert (< x 0))\n(assert (> x 0))\n(check-sat)\n",
    )
    .expect("write smt2");
    // Make the directory read-only so the default `<input>.alethe` write fails
    // (under a non-root test runner — the common CI case).
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o555)).expect("chmod ro");

    let out = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&file)
        .output()
        .expect("spawn ay");

    // Restore permissions so cleanup can remove the directory.
    let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o755));
    let _ = fs::remove_dir_all(&dir);

    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.lines().any(|l| l.trim() == "unsat"),
        "expected `unsat` on stdout, got:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        out.status.success(),
        "a default proof-write failure must keep exit 0 once the verdict is emitted; \
         got exit {:?}\nstderr:\n{stderr}",
        out.status.code()
    );
}
