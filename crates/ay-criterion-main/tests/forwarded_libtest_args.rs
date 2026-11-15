// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression fixture: a Criterion target run by `cargo test` must survive the
//! libtest arguments cargo forwards to every target. Before this crate,
//! `cargo test --all-targets -- --test-threads=1` made every Criterion bench in
//! the workspace exit 2 without running a routine.
//!
//! `harness = false`, so this file is the process cargo runs. It re-runs itself
//! as a Criterion target (the child: its argument list ends in [`ROUTINE`]) on
//! each list below and checks the exit status, that the routine ran, and that
//! it ran in Criterion's test mode rather than being measured. The parent reads
//! none of its own arguments, so it passes under any list cargo forwards to it,
//! including an empty one.

use criterion::{criterion_group, Criterion};
use std::hint::black_box;
use std::process::{Command, Output};

/// The one routine; also the child's filter and the marker of child mode.
const ROUTINE: &str = "forwarded_libtest_args_fixture";

fn routine(c: &mut Criterion) {
    c.bench_function(ROUTINE, |b| b.iter(|| black_box(3_u64).wrapping_mul(7)));
}

criterion_group!(fixture, routine);

/// Lists `cargo test -- …` can forward on which the routine must run in test mode.
const REACH_TEST_MODE: &[&[&str]] = &[
    &[],
    // The reported sweep.
    &["--test-threads=1"],
    &["--test-threads", "4", "--nocapture"],
    // The shape a JSON-reading ledger passes to libtest targets.
    &[
        "-Z",
        "unstable-options",
        "--format",
        "json",
        "--report-time",
        "--show-output",
    ],
    &[
        "-Zunstable-options",
        "--format=junit",
        "--shuffle",
        "--shuffle-seed=7",
        "--no-capture",
    ],
    &["-q", "--include-ignored", "--exact", "--color", "never"],
    &[
        "--fail-fast",
        "--force-run-in-process",
        "--exclude-should-panic",
        "--format",
        "terse",
    ],
    // A skip naming the routine is not honoured: more runs, never fewer.
    &["--skip", ROUTINE],
];

/// Lists Criterion must still refuse (clap's usage error, exit 2) with no
/// routine run: options that add a failure condition, values libtest itself
/// refuses, and arguments neither harness knows.
const REFUSED: &[&[&str]] = &[
    &["--ensure-time"],
    &["--test-threads=0"],
    &["--test-threads", "none"],
    &["-Z", "bogus"],
    &["--format", "xml"],
    &["--no-such-option"],
];

fn run_child(args: &[&str]) -> Output {
    let executable = std::env::current_exe().expect("fixture executable path");
    Command::new(executable)
        .args(args)
        .arg(ROUTINE)
        .output()
        .expect("spawn the fixture as a Criterion target")
}

fn describe(args: &[&str], output: &Output) -> String {
    format!(
        "args {args:?}: {}\n--- stdout\n{}--- stderr\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn check_reaches_test_mode(args: &[&str]) {
    let output = run_child(args);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert!(output.status.success(), "{}", describe(args, &output));
    assert_eq!(
        lines
            .iter()
            .filter(|line| **line == format!("Testing {ROUTINE}"))
            .count(),
        1,
        "the routine must run exactly once; {}",
        describe(args, &output)
    );
    assert!(lines.contains(&"Success"), "{}", describe(args, &output));
    assert!(
        !stdout.contains("Benchmarking"),
        "the routine was measured, not tested; {}",
        describe(args, &output)
    );
}

fn check_refused(args: &[&str]) {
    let output = run_child(args);
    assert_eq!(output.status.code(), Some(2), "{}", describe(args, &output));
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("Testing"),
        "a refused list ran the routine; {}",
        describe(args, &output)
    );
}

fn main() {
    if std::env::args_os().skip(1).any(|arg| arg == ROUTINE) {
        // Child: exactly what `ay_criterion_main::criterion_main!(fixture)` expands to.
        ay_criterion_main::reexec_without_libtest_args();
        fixture();
        Criterion::default().configure_from_args().final_summary();
        return;
    }
    for args in REACH_TEST_MODE {
        check_reaches_test_mode(args);
    }
    for args in REFUSED {
        check_refused(args);
    }
    println!(
        "forwarded_libtest_args: {} forwarded lists reached Criterion's test mode; \
         {} were refused",
        REACH_TEST_MODE.len(),
        REFUSED.len()
    );
}
