// QF_LRA model validation regression (#5534).
//
// Copyright (c) 2026 Andrew Yates Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// #5534: AY historically returned `sat` on EZSMT+ industrial benchmarks
// `1.smt2` and `5.smt2` in the QF_LRA SMT-COMP 2025 set, but the extracted
// model violated ground assertions (e.g. `(= |p(1)| (+ (* |q(1)| 33.0) 2.0))`
// evaluating to false). Z3 correctly returns `unsat` on both. This was a
// soundness bug in the LRA stale-bounds gate (#8187 root cause): the
// `bounds_tightened_since_simplex` flag was cleared by the simplex-completion
// path, and `run_post_simplex_propagation` could re-set it before the
// Sat-return soundness gate fired, leading to a Sat return with stale
// variable values that did not satisfy freshly-asserted direct bounds.
//
// The #8187 fix (commit 53db8e719) split the flag into two semantics and
// demoted the Sat-return path to `Unknown` whenever the post-simplex cascade
// tightened bounds. Both benchmarks now return `unknown` (timeout) rather
// than a false `sat` with model-validation failure.
//
// This test is the permanent regression guard: AY must never report `sat` on
// `1.smt2` or `5.smt2`. `unsat` (correct) or `unknown` (sound) are both
// acceptable.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smtcomp/QF_LRA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );
    if !std::path::Path::new(&benchmark_path).is_file() {
        eprintln!("SKIP: optional QF_LRA benchmark not found: {benchmark_path}");
        return "unknown".to_string();
    }

    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #5534 primary reproducer: `1.smt2` is UNSAT (Z3 confirms). Historically AY
/// returned `sat` with a model-validation failure. After the #8187 fix the
/// stale-bounds path demotes to `unknown`. Either `unsat` or `unknown` is
/// acceptable; `sat` is a soundness regression.
#[test]
#[timeout(60_000)]
fn qf_lra_5534_benchmark_1_never_false_sat() {
    let result = run_ay("1.smt2", 30_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#5534): AY reported 'sat' on benchmarks/smtcomp/QF_LRA/1.smt2 \
         (Z3 confirms UNSAT). Expected 'unsat' or 'unknown'. Result: {result}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on benchmarks/smtcomp/QF_LRA/1.smt2: {result}"
    );
}

/// #5534 secondary reproducer: `5.smt2` is UNSAT (Z3 confirms). Same contract
/// as `1.smt2` — never `sat`.
#[test]
#[timeout(60_000)]
fn qf_lra_5534_benchmark_5_never_false_sat() {
    let result = run_ay("5.smt2", 30_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#5534): AY reported 'sat' on benchmarks/smtcomp/QF_LRA/5.smt2 \
         (Z3 confirms UNSAT). Expected 'unsat' or 'unknown'. Result: {result}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on benchmarks/smtcomp/QF_LRA/5.smt2: {result}"
    );
}
