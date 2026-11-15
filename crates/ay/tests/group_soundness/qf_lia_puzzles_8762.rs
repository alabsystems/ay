// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Soundness regression for QF_LIA cryptarithmetic puzzles tracked under #8762.
//
// Before commit [TL]8762 on disequality_check.rs, SEND+MORE=MONEY returned
// `unknown` after the DPLL(T) loop degraded a Sat result via the model
// validation pipeline (#8373) because the LRA disequality check failed to
// re-evaluate after an Unsat on a violated disequality. These tests pin the
// correctness outcome — they do not enforce the wall-clock target yet
// (acceptance criteria <1s still open on #8762; n-queens n=8 and 9x9 Sudoku
// remain timeouts pending the LIA check-loop latency follow-up).

use std::process::Command;

use crate::corpus::tracked_fixture;

/// Invoke the ay binary with a wall-clock timeout and return the first line of
/// stdout (normalized to `sat` / `unsat` / `unknown`).
///
/// `benchmarks/puzzles` is committed, so a missing puzzle is a broken tree and
/// fails here; it used to be a silent skip that the target read as a pass.
fn run_ay_puzzle(puzzle_file: &str, timeout_ms: u32) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = tracked_fixture(&format!("benchmarks/puzzles/{puzzle_file}"));

    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(benchmark_path.as_os_str())
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// SEND+MORE=MONEY cryptarithmetic: regression for #8762.
///
/// The disequality re-check flag fix (see `disequality_check.rs`) is
/// load-bearing here: without setting `last_diseq_check_had_violation = true`
/// on the LRA Unsat paths, the next LRA check() skipped the disequality scan
/// and returned a spurious Sat with e.g. `S = Y = 8`, which model validation
/// (#8373) then degraded to `unknown`.
///
/// The wall-clock bound is intentionally loose (30s) to guard only the
/// soundness property — performance tuning for the <1s target on #8762 is
/// tracked separately.
#[test]
fn test_send_more_money_sat_8762() {
    let result = run_ay_puzzle("send_more_money.smt2", 30_000);
    assert_eq!(
        result, "sat",
        "SEND+MORE=MONEY must return sat (regression for #8762, disequality \
         re-check flag on LRA Unsat paths); got: {result}"
    );
}
