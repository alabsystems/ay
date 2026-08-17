// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The re-exec supervisor still supervises when forced.
//!
//! `run_wrapped_solve_session` normally forks; the re-exec supervisor is the
//! fallback that converts a solver crash into a sound `unknown` instead of a
//! silent die. Until B5 the only way to force that path was an env var nothing
//! set (`AY_INTERNAL_FORCE_REEXEC_SUPERVISOR`), so the fallback had zero
//! automated coverage on this platform. The override is now the hidden
//! `--force-reexec-supervisor` flag, and this is the coverage it never had.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn scratch() -> (PathBuf, DirGuard) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "ay_reexec_gate_{}_{}",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("sat.cnf"), "p cnf 2 2\n1 2 0\n-1 0\n").unwrap();
    std::fs::write(dir.join("unsat.cnf"), "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    (dir.clone(), DirGuard(dir))
}

/// Under the forced re-exec supervisor, a normal solve must still produce its
/// verdict and exit code — supervision must be transparent when nothing
/// crashes. (SAT: exit 10; UNSAT: exit 20 with a proof written by default.)
#[test]
fn forced_reexec_supervisor_is_transparent_on_healthy_solves() {
    let (dir, _guard) = scratch();
    for (cnf, expect) in [("sat.cnf", 10), ("unsat.cnf", 20)] {
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("solve")
            .arg("--force-reexec-supervisor")
            .arg(dir.join(cnf))
            .output()
            .expect("failed to run ay");
        let code = output.status.code().expect("ay died on a signal");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            code, expect,
            "{cnf}: forced supervisor changed the exit code; stdout: {stdout}"
        );
    }
}
