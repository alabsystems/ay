// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CLI smoke tests for the Model Counting Competition 2026 output surface.

use ntest::timeout;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

struct CleanupGuard(std::path::PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn write_temp_cnf(contents: &str) -> (std::path::PathBuf, CleanupGuard) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let file_id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "ay_model_count_mc2026_{}_{}.cnf",
        std::process::id(),
        file_id
    ));
    std::fs::write(&path, contents).expect("write temp cnf");
    (path.clone(), CleanupGuard(path))
}

fn run_model_count(cnf: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let (path, _cleanup) = write_temp_cnf(cnf);
    let output = Command::new(ay_path)
        .arg("model-count")
        .arg(&path)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("spawn ay model-count");

    assert!(
        output.status.success(),
        "ay model-count exited non-zero: status={:?}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
#[timeout(30_000)]
fn model_count_emits_exact_unweighted_mc_count() {
    let stdout = run_model_count("c t mc\np cnf 2 2\n1 2 0\n-1 -2 0\n");

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type mc"), "{stdout}");
    assert!(
        stdout.contains("c s log10-estimate 0.301029995663981"),
        "{stdout}"
    );
    assert!(stdout.contains("c s exact arb int 2"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn model_count_collapses_projected_assignments() {
    let stdout = run_model_count("c t pmc\nc p show 1 0\np cnf 3 2\n1 0\n2 3 0\n");

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type pmc"), "{stdout}");
    assert!(
        stdout.contains("c s log10-estimate 0.000000000000000"),
        "{stdout}"
    );
    assert!(stdout.contains("c s exact arb int 1"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn model_count_translates_dimacs_projection_vars_to_sat_indices() {
    let stdout = run_model_count("c t pmc\nc p show 2 0\np cnf 2 1\n1 0\n");

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type pmc"), "{stdout}");
    assert!(stdout.contains("c s exact arb int 2"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn model_count_reports_zero_as_unsat() {
    let stdout = run_model_count("c t mc\np cnf 1 2\n1 0\n-1 0\n");

    assert!(stdout.contains("s UNSATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type mc"), "{stdout}");
    assert!(stdout.contains("c s log10-estimate -inf"), "{stdout}");
    assert!(stdout.contains("c s exact arb int 0"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn model_count_solves_weighted_tracks_exactly() {
    // One free variable with w(1)=0.5 (complement defaults to 0.5):
    // weighted count = 0.5 + 0.5 = 1.
    let stdout = run_model_count("c t pwmc\nc p weight 1 0.5 0\np cnf 1 0\n");

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type pwmc"), "{stdout}");
    assert!(stdout.contains("c s exact arb frac 1/1"), "{stdout}");
}

#[test]
#[timeout(30_000)]
fn model_count_solves_wmc_with_negative_weights() {
    // (x1 ∨ x2), w(x1)=-1/2, w(-x1)=3/2, x2 unweighted.
    // Models: TT=-1/2, TF=-1/2, FT=3/2 → total 1/2.
    let stdout =
        run_model_count("c t wmc\nc p weight 1 -1/2 0\nc p weight -1 3/2 0\np cnf 2 1\n1 2 0\n");

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type wmc"), "{stdout}");
    assert!(stdout.contains("c s exact arb frac 1/2"), "{stdout}");
    assert!(
        stdout.contains("c s log10-estimate -0.301029995663981"),
        "{stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn model_count_solves_amc_complex_spec_example_5() {
    let stdout = run_model_count(
        "p cnf 3 2\nc t amc-complex\n\
         c p weight 1 0.4+0.2i 0\nc p weight -1 0.6+0.6i 0\n\
         c p weight 2 0.5+0.5i 0\nc p weight -2 0.5+0.5i 0\n\
         c p weight 3 0.3+0.7i 0\nc p weight -3 0.7+0.3i 0\n\
         1 -2 0\n-1 3 0\n",
    );

    assert!(stdout.contains("s SATISFIABLE"), "{stdout}");
    assert!(stdout.contains("c s type amc-complex"), "{stdout}");
    // The spec PDF's printed answer (0.55-1.1i) contradicts its own weight
    // function; the true sum over the 4 models is -24/25 + 23/25 i (verified
    // by independent brute force; the same convention reproduces the spec's
    // wmc Example 2 exactly: 173/500 = 0.346).
    assert!(stdout.contains("c s neglog10-estimate-real"), "{stdout}");
    assert!(
        stdout.contains("c s exact arb frac -24/25+23/25i"),
        "{stdout}"
    );
}
