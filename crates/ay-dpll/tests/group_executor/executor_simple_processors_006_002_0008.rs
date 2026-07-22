// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression test for P0 SAT soundness bug #1818.
//!
//! `simple_processors_006_002_0008.smt2` was incorrectly reported SAT due to
//! missing propagation after watch reinitialization.
//!
//! This test only runs in release mode (~40s). Debug mode would timeout.
//! The benchmark file is not checked into the repo — the test exits early
//! with a diagnostic message when the file is absent.

#[cfg(not(debug_assertions))]
use ay_dpll::Executor;
#[cfg(not(debug_assertions))]
use ay_frontend::parse;
#[cfg(not(debug_assertions))]
use ntest::timeout;

#[cfg(not(debug_assertions))]
#[test]
#[timeout(120_000)] // Takes ~40s in release mode, allow 2x margin
fn test_executor_simple_processors_006_002_0008_unsat() {
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../benchmarks/smtcomp/QF_BV/simple_processors_006_002_0008.smt2");
    let input = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            eprintln!(
                "SKIP: benchmark file not found: {}. \
                 Download QF_BV benchmarks to run this regression test.",
                path.display()
            );
            return;
        }
        Err(e) => panic!("read simple_processors_006_002_0008.smt2: {e}"),
    };

    let commands = parse(&input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}
