// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ay <query> --proof <file>` on a datatype constructor spelled `||`, the
//! empty SMT-LIB symbol, prints `unsat` with `unsat_admission=strict-proof`
//! and no `self-check-rejected` on stderr, as for its twin spelled `a`.

use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const EMPTY_CONSTRUCTOR: &str = "(declare-datatypes ((E 0)) (((||) (b))))\n\
    (assert (= || b))\n\
    (check-sat)\n";

const TWIN: &str = "(declare-datatypes ((E 0)) (((a) (b))))\n\
    (assert (= a b))\n\
    (check-sat)\n";

/// `ay <query> --proof <file>`: its stdout and stderr.
fn run(query: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("query.smt2");
    std::fs::write(&input, query).expect("write the query");
    let proof = dir.path().join("query.alethe");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&input)
        .arg("--proof")
        .arg(&proof)
        .current_dir(dir.path())
        .output_timeout(Duration::from_secs(60))
        .expect("ay finishes within the child deadline");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn an_empty_constructor_is_admitted_like_its_twin() {
    for (label, query) in [("twin", TWIN), ("empty", EMPTY_CONSTRUCTOR)] {
        let (stdout, stderr) = run(query);
        assert_eq!(stdout.trim(), "unsat", "{label}: stderr={stderr}");
        assert!(
            stderr.contains("unsat_admission=strict-proof"),
            "{label}: stderr={stderr}"
        );
        assert!(
            !stderr.contains("self-check-rejected"),
            "{label}: stderr={stderr}"
        );
    }
}
