// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion-order determinism guard.
//!
//! Part of #8719 (Z3 #1618 class). A correct SMT solver must return the same
//! answer regardless of the order in which independent assertions are added.
//! This integration test runs a small corpus of SMT-LIB fixtures, permutes
//! their top-level `(assert ...)` blocks `N = 10` times, and asserts that
//! `ay` returns the same answer for every permutation and across repeated
//! runs.
//!
//! Scope:
//!   * Fixtures embedded inline — 6 formulas spanning 5 SMT-LIB logics
//!     (QF_LIA sat + unsat, QF_LRA, QF_BV, QF_ABV, QF_UF).
//!   * Permutations: 10 distinct deterministic orderings per fixture. The
//!     ordering set is seeded with structural permutations (identity,
//!     reverse, rotations) and filled via a fixed-seed Fisher-Yates shuffle.
//!     The seed is a compile-time constant so the test is reproducible.
//!     We use a deterministic permutation driver rather than `proptest`
//!     because the *property under test is determinism* — the driver itself
//!     must therefore be deterministic (a random driver would make failure
//!     triage harder without adding coverage).
//!   * Runs: 3 repetitions per original fixture to catch run-to-run drift
//!     (e.g. random seed leakage, PRNG state seeded from wall-clock).
//!   * Assertion: every run on every permutation yields the same sat/unsat
//!     answer as the oracle. Models are NOT compared (permuted assertions
//!     legitimately allow different witnesses).
//!   * Proof-hash comparison: deliberately out of scope in this pass.
//!     `ay` accepts `--proof FILE`, but DRAT/Alethe proofs are sensitive to
//!     decision order — two sound proofs of the same UNSAT instance can be
//!     byte-different even on deterministic runs. A stronger "semantic
//!     proof-equivalence" check would require normalising proofs, which is
//!     future work. See #8719 for tracking.
//!   * Timing: we measure wall-clock time per run and emit a `WARN` to
//!     stderr when any permutation exceeds `2x` the median for that fixture.
//!     We do **not** fail on timing jitter — subprocess startup, macOS
//!     Spotlight throttling, and shared CI runners make sub-second timing
//!     too noisy to gate correctness. The warning helps surface adversarial
//!     orderings that tickle a pathological solver path.
//!
//! If this test fails on `answer`, the cause is non-deterministic behaviour
//! in the solver. File a follow-up with the `determinism` label (see issue
//! #8719). Do not mask with retries or randomisation.

#[path = "assertion_order_determinism_8719/support.rs"]
mod support;

use ntest::timeout;
use std::time::Duration;
use support::{permutations, rebuild, run_ay, run_ay_timed, split_script, TempFile, FIXTURES};

fn ay_bin() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// Number of permutations tested per fixture (issue #8719 specifies N=10).
const PERMUTATIONS_PER_FIXTURE: usize = 10;

/// Number of independent runs on the *original* script used for run-to-run
/// stability. Permutation coverage is handled separately.
const RUNS_PER_FIXTURE: usize = 3;

// ---------------------------------------------------------------------------
// Integration tests (spawn ay as a subprocess)
// ---------------------------------------------------------------------------

/// For each fixture: run the original script `RUNS_PER_FIXTURE` times and
/// assert the answer matches the oracle and is byte-identical across runs.
/// Establishes run-to-run determinism independent of permutation effects.
#[test]
#[timeout(180_000)]
fn assertion_order_determinism_run_stability() {
    let ay = ay_bin();
    for fixture in FIXTURES {
        let fixture_name = fixture.name;
        let expected_str = fixture.expected.as_str();
        let tmp = TempFile::new(fixture.source, fixture_name);
        let mut answers: Vec<String> = Vec::with_capacity(RUNS_PER_FIXTURE);
        for run in 0..RUNS_PER_FIXTURE {
            let ans = run_ay(ay, tmp.path());
            assert_eq!(
                ans, expected_str,
                "fixture {fixture_name} run {run} expected {expected_str} but got {ans}",
            );
            answers.push(ans);
        }
        let first = answers[0].clone();
        for (idx, ans) in answers.iter().enumerate().skip(1) {
            assert_eq!(
                ans, &first,
                "fixture {fixture_name}: run {idx} produced {ans} but run 0 produced {first}"
            );
        }
    }
}

/// For each fixture: split assertions, build `PERMUTATIONS_PER_FIXTURE`
/// distinct permutations, and assert `ay` returns the same (expected) answer
/// for each. This is the core assertion-order guard for #8719.
///
/// Timing is measured and a `WARN` is emitted to stderr if any permutation
/// takes >2x the median time — advisory only (see module docs).
#[test]
#[timeout(300_000)]
fn assertion_order_determinism_permutation_stability() {
    let ay = ay_bin();
    for fixture in FIXTURES {
        let fixture_name = fixture.name;
        let split = split_script(fixture.source);
        let assert_count = split.assertions.len();
        assert!(
            assert_count >= 2,
            "fixture {fixture_name} must have >= 2 assertions to exercise permutation (got {assert_count})",
        );
        let perms = permutations(assert_count, PERMUTATIONS_PER_FIXTURE);
        let distinct = perms.len();
        assert!(
            distinct >= PERMUTATIONS_PER_FIXTURE.min(factorial(assert_count)),
            "fixture {fixture_name} with {assert_count} assertions produced only {distinct} distinct permutations (want {PERMUTATIONS_PER_FIXTURE})",
        );
        let expected_str = fixture.expected.as_str();
        let mut elapsed: Vec<Duration> = Vec::with_capacity(distinct);
        for (i, order) in perms.iter().enumerate() {
            let rebuilt = rebuild(&split, order);
            let tag = format!("{fixture_name}_perm{i}");
            let tmp = TempFile::new(&rebuilt, &tag);
            let outcome = run_ay_timed(ay, tmp.path());
            assert_eq!(
                outcome.answer, expected_str,
                "fixture {fixture_name} permutation #{i} (order {order:?}) returned {} but expected {expected_str}\nrebuilt source:\n{rebuilt}",
                outcome.answer,
            );
            elapsed.push(outcome.elapsed);
        }
        warn_on_timing_skew(fixture_name, &elapsed);
    }
}

/// Compute the median (lower-median) of a slice of durations and emit a
/// `WARN` for any sample that exceeds `2x` the median. Advisory only —
/// subprocess startup and host noise make sub-second timing unreliable.
fn warn_on_timing_skew(fixture_name: &str, samples: &[Duration]) {
    if samples.len() < 3 {
        return;
    }
    let mut sorted: Vec<Duration> = samples.to_vec();
    sorted.sort();
    let median = sorted[sorted.len() / 2];
    // Floor at 100ms — below that, subprocess startup dominates and the
    // "2x median" gate is meaningless.
    let floor = Duration::from_millis(100);
    let effective_median = median.max(floor);
    let threshold = effective_median.saturating_mul(2);
    for (i, &t) in samples.iter().enumerate() {
        if t > threshold {
            eprintln!(
                "WARN [#8719] fixture {fixture_name} permutation {i} took {t:?} \
                 (median {median:?}, threshold {threshold:?}) — possible \
                 order-sensitive performance regression"
            );
        }
    }
}

fn factorial(n: usize) -> usize {
    (1..=n).product::<usize>().max(1)
}

// ---------------------------------------------------------------------------
// Unit tests for the splitter and permutation helpers (no subprocess)
// ---------------------------------------------------------------------------

#[test]
fn splitter_extracts_top_level_asserts() {
    let src = "(set-logic QF_LIA)\n\
               (declare-const x Int)\n\
               (assert (>= x 0))\n\
               (assert (<= x 10))\n\
               (check-sat)\n";
    let split = split_script(src);
    assert_eq!(split.assertions.len(), 2);
    assert_eq!(split.assertions[0], "(assert (>= x 0))");
    assert_eq!(split.assertions[1], "(assert (<= x 10))");
    assert!(split.prelude.contains("(set-logic QF_LIA)"));
    assert!(split.prelude.contains("(declare-const x Int)"));
    assert!(split.epilogue.contains("(check-sat)"));
}

#[test]
fn splitter_handles_nested_parens_in_assert() {
    let src = "(set-logic QF_LIA)\n\
               (declare-const x Int)\n\
               (declare-const y Int)\n\
               (assert (and (>= x 0) (<= y (+ x 1))))\n\
               (check-sat)\n";
    let split = split_script(src);
    assert_eq!(split.assertions.len(), 1);
    assert_eq!(
        split.assertions[0],
        "(assert (and (>= x 0) (<= y (+ x 1))))"
    );
}

#[test]
fn splitter_ignores_assert_keyword_in_comment() {
    let src = "(set-logic QF_LIA)\n\
               ; (assert (= 1 2))\n\
               (declare-const x Int)\n\
               (assert (>= x 0))\n\
               (check-sat)\n";
    let split = split_script(src);
    assert_eq!(split.assertions.len(), 1);
    assert_eq!(split.assertions[0], "(assert (>= x 0))");
}

#[test]
fn rebuild_with_identity_order_is_equivalent() {
    let src = "(set-logic QF_LIA)\n\
               (declare-const x Int)\n\
               (assert (>= x 0))\n\
               (assert (<= x 10))\n\
               (check-sat)\n";
    let split = split_script(src);
    let rebuilt = rebuild(&split, &[0, 1]);
    assert!(rebuilt.contains("(set-logic QF_LIA)"));
    assert!(rebuilt.contains("(assert (>= x 0))"));
    assert!(rebuilt.contains("(assert (<= x 10))"));
    assert!(rebuilt.contains("(check-sat)"));
    let pos0 = rebuilt.find("(assert (>= x 0))").unwrap();
    let pos1 = rebuilt.find("(assert (<= x 10))").unwrap();
    assert!(pos0 < pos1);
}

#[test]
fn rebuild_with_reversed_order_swaps_asserts() {
    let src = "(set-logic QF_LIA)\n\
               (declare-const x Int)\n\
               (assert (>= x 0))\n\
               (assert (<= x 10))\n\
               (check-sat)\n";
    let split = split_script(src);
    let rebuilt = rebuild(&split, &[1, 0]);
    let pos0 = rebuilt.find("(assert (>= x 0))").unwrap();
    let pos1 = rebuilt.find("(assert (<= x 10))").unwrap();
    assert!(pos1 < pos0, "expected reversed order but got:\n{rebuilt}");
}

#[test]
fn permutations_are_distinct() {
    let perms = permutations(4, 10);
    for (i, p) in perms.iter().enumerate() {
        for (j, q) in perms.iter().enumerate() {
            if i != j {
                assert_ne!(p, q, "permutations {i} and {j} are equal: {p:?}");
            }
        }
    }
}

#[test]
fn permutations_cover_all_indices() {
    let perms = permutations(5, 10);
    for p in &perms {
        let mut sorted = p.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..5).collect::<Vec<_>>());
    }
}

#[test]
fn permutations_generate_ten_distinct_for_n_5() {
    // 5! = 120 >> 10, so the driver must deliver 10 distinct permutations.
    let perms = permutations(5, 10);
    assert_eq!(
        perms.len(),
        10,
        "expected 10 distinct permutations for n=5, got {}: {:?}",
        perms.len(),
        perms
    );
}

#[test]
fn permutations_generate_ten_distinct_for_n_6() {
    let perms = permutations(6, 10);
    assert_eq!(
        perms.len(),
        10,
        "expected 10 distinct permutations for n=6, got {}: {:?}",
        perms.len(),
        perms
    );
}

#[test]
fn permutations_saturate_at_factorial_for_small_n() {
    // n=3 → 3! = 6 distinct permutations; asking for 10 must return all 6.
    let perms = permutations(3, 10);
    assert_eq!(
        perms.len(),
        6,
        "expected 6 (= 3!) distinct perms, got {}: {:?}",
        perms.len(),
        perms
    );
    // All 6 permutations of {0,1,2} must be present.
    let mut all: Vec<Vec<usize>> = vec![
        vec![0, 1, 2],
        vec![0, 2, 1],
        vec![1, 0, 2],
        vec![1, 2, 0],
        vec![2, 0, 1],
        vec![2, 1, 0],
    ];
    let mut got = perms;
    all.sort();
    got.sort();
    assert_eq!(got, all);
}

#[test]
fn permutations_are_deterministic_across_calls() {
    // Re-invocation with the same arguments must produce the same sequence.
    // This is the contract that makes failure triage possible.
    let a = permutations(6, 10);
    let b = permutations(6, 10);
    assert_eq!(a, b, "permutations() is not deterministic across calls");
}
