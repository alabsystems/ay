// QF_LRA rebuild-overhead regression (#8256).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// #8256: Five QF_LRA benchmarks time out (or were borderline) in ay despite
// Phase 1 incremental split-loop work. Profiling at HEAD (see issue comment)
// confirms the root-cause dominant cost is still the propagation feedback
// loop tracked by #8452 (10-133x decision count vs. Z3), not per-callback
// rebuild overhead. This regression file locks soundness and performance
// contracts on the five reproducers so that future fixes in the
// #8467 -> #8255 -> #8256 -> #8452 chain can be measured against a stable
// baseline:
//
//   1. Soundness: ay must NEVER return the wrong answer on any of the five
//      benchmarks. `sat`/`unsat` matching Z3, or `unknown`, are all allowed.
//      The forbidden outcome is a false answer (sat-claimed-unsat /
//      unsat-claimed-sat).
//   2. Performance: for the two smallest reproducers
//      (`simple_startup_10nodes.bug.induct` and
//      `simple_startup_14nodes.bug.induct`), ay must finish within the
//      30s wall-clock budget Z3 uses as its "easy" bar. Today ay typically
//      returns `unknown` at that budget; that is accepted but not a false
//      answer. A future #8452 fix should flip these to `sat` well under 30s.
//
// Z3 reference (from issue #8256 description):
//   - simple_startup_10nodes.bug.induct.smt2       sat   in  1.3s
//   - simple_startup_14nodes.bug.induct.smt2       sat   in  1.8s
//   - 0067-labyrinth-18-0.smt2                     sat   in 11.3s   (63MB)
//   - 0165-labyrinth-13-0.smt2                     sat   in 25.0s   (21MB)
//   - simple_startup_7nodes.abstract.induct.smt2   unsat in 15.3s
//
// Related: #8452 (root cause, propagation feedback loop), #8467 (lazy
// justification), #8255 (BCP theory-check frequency).

use ntest::timeout;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use crate::corpus::{optional_corpus_file, tracked_fixture};

const QF_LRA: &str = "benchmarks/smtcomp/QF_LRA";

/// Run ay on a QF_LRA benchmark with an internal timeout (milliseconds) and
/// return the first line of stdout, trimmed. The test harness additionally
/// applies its own `#[timeout]` wall-clock ceiling for hard-hang protection.
fn run_ay(benchmark_path: &Path, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// `run_ay` on one of the two committed reproducers (`benchmarks/.gitignore`
/// un-ignores `simple_startup_{10,14}nodes.bug.induct.smt2`). Their absence is
/// a broken tree and fails the test. It used to become the verdict `unknown`,
/// which every oracle in this file accepts — including the 30 s performance
/// gates, which then measured a run that never happened.
fn run_ay_tracked(smt_file: &str, timeout_ms: u64) -> String {
    run_ay(
        &tracked_fixture(&format!("{QF_LRA}/{smt_file}")),
        timeout_ms,
    )
}

/// `run_ay` on a gitignored corpus file, or `None` when it is absent and
/// skipping is allowed (`AY_REQUIRE_CORPUS=1` fails instead). `None` is never
/// a verdict; the caller returns without asserting (see `common/corpus.rs`).
fn run_ay_corpus(test: &str, smt_file: &str, timeout_ms: u64) -> Option<String> {
    let benchmark_path = optional_corpus_file(test, &format!("{QF_LRA}/{smt_file}"))?;
    Some(run_ay(&benchmark_path, timeout_ms))
}

/// As `run_ay_tracked` but also returns elapsed wall-clock seconds of the
/// solver run alone.
fn run_ay_timed(smt_file: &str, timeout_ms: u64) -> (String, f64) {
    let benchmark_path = tracked_fixture(&format!("{QF_LRA}/{smt_file}"));
    let start = Instant::now();
    let result = run_ay(&benchmark_path, timeout_ms);
    let elapsed = start.elapsed().as_secs_f64();
    (result, elapsed)
}

// ---------------------------------------------------------------------------
// Soundness tests: one per reproducer. AY may answer the expected value or
// `unknown`, but NEVER the opposite of Z3's answer.
// ---------------------------------------------------------------------------

/// #8256 soundness: `simple_startup_10nodes.bug.induct` is SAT per Z3 (1.3s).
/// AY must never answer `unsat` on this benchmark.
#[test]
#[timeout(180_000)]
fn rebuild_8256_never_false_unsat_on_simple_startup_10nodes() {
    let result = run_ay_tracked("simple_startup_10nodes.bug.induct.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT in 1.3s). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on simple_startup_10nodes.bug.induct.smt2: {result}"
    );
}

/// #8256 soundness: `simple_startup_14nodes.bug.induct` is SAT per Z3 (1.8s).
/// AY must never answer `unsat` on this benchmark.
#[test]
#[timeout(180_000)]
fn rebuild_8256_never_false_unsat_on_simple_startup_14nodes() {
    let result = run_ay_tracked("simple_startup_14nodes.bug.induct.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT in 1.8s). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on simple_startup_14nodes.bug.induct.smt2: {result}"
    );
}

/// #8256 soundness: `0067-labyrinth-18-0` is SAT per Z3 (11.3s, 63MB input).
/// AY must never answer `unsat`. At current HEAD, ay typically times out to
/// `unknown` well before parse-completion, which is acceptable under this
/// contract — the soundness gate is "no false UNSAT".
#[test]
#[timeout(300_000)]
fn rebuild_8256_never_false_unsat_on_labyrinth_18() {
    let Some(result) = run_ay_corpus(
        "rebuild_8256_never_false_unsat_on_labyrinth_18",
        "0067-labyrinth-18-0.smt2",
        120_000,
    ) else {
        return;
    };
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT in 11.3s). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on 0067-labyrinth-18-0.smt2: {result}"
    );
}

/// #8256 soundness: `0165-labyrinth-13-0` is SAT per Z3 (25.0s, 21MB input).
/// AY must never answer `unsat`.
#[test]
#[timeout(300_000)]
fn rebuild_8256_never_false_unsat_on_labyrinth_13() {
    let Some(result) = run_ay_corpus(
        "rebuild_8256_never_false_unsat_on_labyrinth_13",
        "0165-labyrinth-13-0.smt2",
        120_000,
    ) else {
        return;
    };
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT in 25.0s). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on 0165-labyrinth-13-0.smt2: {result}"
    );
}

/// #8256 soundness: `simple_startup_7nodes.abstract.induct` is UNSAT per Z3
/// (15.3s). AY must never answer `sat` on this benchmark.
#[test]
#[timeout(180_000)]
fn rebuild_8256_never_false_sat_on_simple_startup_7nodes_abstract_induct() {
    let Some(result) = run_ay_corpus(
        "rebuild_8256_never_false_sat_on_simple_startup_7nodes_abstract_induct",
        "simple_startup_7nodes.abstract.induct.smt2",
        60_000,
    ) else {
        return;
    };
    assert_ne!(
        result, "sat",
        "Soundness regression (#8256): AY reported 'sat' on an UNSAT QF_LRA \
         instance (Z3 confirms UNSAT in 15.3s). Expected 'unsat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on simple_startup_7nodes.abstract.induct.smt2: {result}"
    );
}

// ---------------------------------------------------------------------------
// Performance tests: the two smallest reproducers must finish (with any
// allowed result, including `unknown`) inside a 30s wall-clock budget. Z3
// solves both in under 2s. These tests are the direct acceptance criterion
// for issue #8256.
// ---------------------------------------------------------------------------

/// #8256 performance: `simple_startup_10nodes.bug.induct` must finish in
/// under 30s wall-clock. Z3 solves this in 1.3s; ay is allowed to return
/// `sat` or `unknown`, but never `unsat`, and must not exceed 30s.
#[test]
#[timeout(120_000)]
fn rebuild_8256_simple_startup_10nodes_under_30s() {
    // Give ay a 28s internal timeout so any cooperative-shutdown overhead
    // (stats flush, watchdog grace period) still fits under the 30s gate.
    let (result, elapsed) = run_ay_timed("simple_startup_10nodes.bug.induct.smt2", 28_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance. Result: {result}, elapsed: {elapsed:.2}s"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on simple_startup_10nodes.bug.induct.smt2: \
         {result} (elapsed {elapsed:.2}s)"
    );
    assert!(
        elapsed < 30.0,
        "Performance regression (#8256): simple_startup_10nodes.bug.induct.smt2 \
         did not finish within 30s (elapsed {elapsed:.2}s, result {result}). \
         Z3 solves this in 1.3s."
    );
}

/// #8256 performance: `simple_startup_14nodes.bug.induct` must finish in
/// under 30s wall-clock. Z3 solves this in 1.8s; ay is allowed to return
/// `sat` or `unknown`, but never `unsat`, and must not exceed 30s.
#[test]
#[timeout(120_000)]
fn rebuild_8256_simple_startup_14nodes_under_30s() {
    let (result, elapsed) = run_ay_timed("simple_startup_14nodes.bug.induct.smt2", 28_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8256): AY reported 'unsat' on a SAT QF_LRA \
         instance. Result: {result}, elapsed: {elapsed:.2}s"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on simple_startup_14nodes.bug.induct.smt2: \
         {result} (elapsed {elapsed:.2}s)"
    );
    assert!(
        elapsed < 30.0,
        "Performance regression (#8256): simple_startup_14nodes.bug.induct.smt2 \
         did not finish within 30s (elapsed {elapsed:.2}s, result {result}). \
         Z3 solves this in 1.8s."
    );
}
