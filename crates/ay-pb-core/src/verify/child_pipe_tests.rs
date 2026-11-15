// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The optimality check against a z3 that exits without reading its query.
//!
//! This crate is built with the `unix_hardened` Trust profile, whose `main`
//! runs with SIGPIPE at `SIG_DFL`: writing the query through a plain
//! `ChildStdin` to a z3 that had already exited killed the verifier (`ay-pb pb
//! verify`) with exit 141 before the `Z3Error::Io` path could report the check
//! inconclusive. The scenario runs alone ([`run_alone_with`]), where a
//! bypass of `ChildPipeWriter` is a SIGPIPE death named as one, with `Z3_PATH`
//! naming the fake z3 in the re-exec only.

use super::*;
use crate::types::{PbLit, PbTerm};
use ay_test_support::sigpipe::run_alone_with;

/// A z3 that proves its identity (`--version` prints the banner, the
/// `--z3-mode --version` negative control fails) and exits at once on a query,
/// reading none of it.
const EXITS_UNREAD_Z3: &str = "#!/bin/sh\n\
case \"$*\" in\n\
  '--version') echo 'Z3 version 4.13.0 - 64 bit'; exit 0 ;;\n\
  '--z3-mode --version') exit 1 ;;\n\
esac\n\
exit 0\n";

/// Every `FakeZ3` directory is named with this prefix.
const FAKE_Z3_DIR_PREFIX: &str = "ay-pb-verify-fake-z3-";

/// The fake z3 in a directory this test owns.
struct FakeZ3 {
    directory: std::path::PathBuf,
}

impl FakeZ3 {
    fn new() -> Self {
        use std::os::unix::fs::PermissionsExt as _;
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        // A killed test process never removed its fixture, and a later one can
        // reuse its PID: take the next id rather than touch that directory.
        let directory = loop {
            let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
            let candidate = std::env::temp_dir()
                .join(format!("{FAKE_Z3_DIR_PREFIX}{}-{id}", std::process::id()));
            match std::fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => panic!("create fake-z3 directory: {error}"),
            }
        };
        let z3 = directory.join("z3");
        std::fs::write(&z3, EXITS_UNREAD_Z3).expect("write fake z3");
        std::fs::set_permissions(&z3, std::fs::Permissions::from_mode(0o755))
            .expect("make fake z3 executable");
        Self { directory }
    }

    fn path(&self) -> std::path::PathBuf {
        self.directory.join("z3")
    }
}

impl Drop for FakeZ3 {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

/// `min x1 + ... + xn  s.t.  x1 + ... + xn >= 1`, wide enough that its z3
/// query is several times a pipe buffer: the write is parked on the full pipe
/// when z3 exits, whatever the scheduling.
fn wide_instance(num_vars: u32) -> PbInstance {
    let terms: Vec<PbTerm> = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    PbInstance {
        num_vars,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: terms.clone(),
            rel: PbRel::Ge,
            rhs: 1,
        }],
        objective: Some(PbObjective { terms }),
    }
}

#[test]
fn optimality_check_against_a_z3_that_exits_unread_is_inconclusive_not_a_kill() {
    let fake = FakeZ3::new();
    let z3 = fake.path();
    if !run_alone_with(
        module_path!(),
        "optimality_check_against_a_z3_that_exits_unread_is_inconclusive_not_a_kill",
        |command| {
            command.env("Z3_PATH", &z3);
        },
    )
    .expect("re-exec this test alone")
    {
        return;
    }
    // The oracle is the fake only when the harness set `Z3_PATH` for this
    // re-exec; run by hand without it, a real z3 would answer and the
    // scenario would test nothing.
    let oracle = std::env::var_os("Z3_PATH").map(std::path::PathBuf::from);
    assert!(
        oracle
            .as_deref()
            .and_then(std::path::Path::parent)
            .and_then(std::path::Path::file_name)
            .is_some_and(|dir| dir.to_string_lossy().starts_with(FAKE_Z3_DIR_PREFIX)),
        "Z3_PATH must name a fake z3 from FakeZ3 (run this test through its \
         harness, not by hand): {oracle:?}"
    );
    let instance = wide_instance(8_000);
    let smt = emit_smt2_better_than(
        &instance,
        instance.objective.as_ref().expect("objective"),
        1,
    )
    .expect("in-range bound");
    assert!(
        smt.len() > 256 * 1024,
        "the query must outgrow a pipe buffer"
    );

    let mut solution = String::from("s OPTIMUM FOUND\no 1\nv x1");
    for var in 2..=8_000 {
        solution.push_str(&format!(" -x{var}"));
    }
    solution.push('\n');
    let output = parse_solver_output(&solution, instance.num_vars);
    let report = verify(&instance, &output, Z3Mode::Require, 30);
    match report.optimality() {
        OptimalityCheck::Inconclusive(detail) => assert!(
            detail.contains("writing the query to z3 failed"),
            "the check names the dead z3: {detail}"
        ),
        other => panic!("a z3 that read nothing decides nothing: {other:?}"),
    }
    assert!(!report.is_verified());
}
