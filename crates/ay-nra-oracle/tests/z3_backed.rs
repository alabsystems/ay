// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI regressions that do not guess a machine-specific reference library.
//!
//! Live verification is deliberately explicit. Run the binary with a trusted
//! path, for example:
//!
//! ```text
//! ay-nra-oracle probe --z3 /path/to/libz3
//! ay-nra-oracle golden --heavy --z3 /path/to/libz3
//! ay-nra-oracle selftest --seed 11 --cases 1600 --z3 /path/to/libz3
//! ay-nra-oracle fuzz --seed 424242 --cases 1200 --progress 0 --z3 /path/to/libz3
//! ```

use std::process::{Command, Output};

fn oracle(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ay-nra-oracle"))
        .args(args)
        .output()
        .expect("oracle binary runs")
}

#[test]
fn path_free_golden_fixtures_run_without_z3() {
    let out = oracle(&["golden", "--no-z3"]);
    assert!(
        out.status.success(),
        "path-free golden failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn reference_modes_require_an_explicit_z3_path() {
    for command in ["probe", "fuzz", "repro", "selftest", "dbg"] {
        let out = oracle(&[command]);
        assert_eq!(out.status.code(), Some(64), "{command} unexpectedly ran");
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("requires --z3 PATH"),
            "unexpected {command} diagnostic: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn an_explicit_unloadable_reference_is_a_fatal_error() {
    let out = oracle(&["probe", "--z3", "/definitely/not/a/reference/libz3.so"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("could not load the reference libz3"));
}
