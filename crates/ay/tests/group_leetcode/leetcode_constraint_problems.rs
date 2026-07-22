// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LeetCode-style constraint programming problems encoded as SMT-LIB2.
//! Each test runs ay on an .smt2 file and validates the result.
//!
//! Inspired by Hillel Wayne's "Solving Advent of Code with SMT" and
//! constraint programming approaches to classic algorithm problems.
//!
//! Problems:
//!   - Two Sum (LeetCode #1)
//!   - Coin Change (LeetCode #322) with optimality proof
//!   - Best Time to Buy and Sell Stock (LeetCode #121) with optimality proof
//!   - Three Sum variant (LeetCode #15)
//!   - Largest Rectangle in Histogram (LeetCode #84) with optimality proof
//!   - N-Queens N=5 (LeetCode #51)
//!   - Graph Coloring (classic CSP)

use ntest::timeout;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Root of the ay repository (the workspace root, not the crate root).
fn repo_root() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    Path::new(manifest_dir)
        .parent()
        .expect("crate should be inside workspace")
        .parent()
        .expect("crates/ should be inside workspace root")
        .to_path_buf()
}

/// Path to the leetcode test fixtures directory.
fn leetcode_dir() -> PathBuf {
    repo_root().join("tests").join("leetcode")
}

/// Run ay on an SMT-LIB2 file and return (stdout, stderr, success).
fn run_ay(smt2_file: &Path) -> (String, String, bool) {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(smt2_file)
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn ay: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr, output.status.success())
}

/// Assert that ay returns "sat" and the model contains expected variable bindings.
fn assert_sat_with_model(smt2_file: &str, expected_bindings: &[(&str, &dyn Fn(i64) -> bool)]) {
    let path = leetcode_dir().join(smt2_file);
    let (stdout, stderr, success) = run_ay(&path);

    assert!(success, "ay failed on {smt2_file}: stderr={stderr}");

    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(
        first_line, "sat",
        "expected sat for {smt2_file}, got: {first_line}\nstderr: {stderr}"
    );

    // Parse model bindings from (define-fun name () Int value)
    for (var_name, predicate) in expected_bindings {
        let pattern = format!("(define-fun {var_name} () Int ");
        let binding = stdout
            .lines()
            .find(|line| line.contains(&pattern))
            .unwrap_or_else(|| {
                panic!("model missing binding for '{var_name}' in {smt2_file}\nmodel:\n{stdout}")
            });

        // Extract the integer value: "(define-fun x () Int 42)" -> 42
        // Handle negative values like "(- 1)"
        let trimmed = binding.trim();
        let after_prefix = trimmed
            .strip_prefix(&format!("(define-fun {var_name} () Int "))
            .unwrap_or_else(|| panic!("could not parse binding for '{var_name}': '{trimmed}'"));
        // Strip the trailing ')' from the define-fun
        let value_str = after_prefix
            .strip_suffix(')')
            .unwrap_or_else(|| panic!("could not strip suffix for '{var_name}': '{after_prefix}'"));

        let value: i64 = if value_str.starts_with("(- ") {
            // SMT-LIB negative: (- N)
            let inner = value_str
                .strip_prefix("(- ")
                .unwrap()
                .strip_suffix(')')
                .unwrap();
            -inner.parse::<i64>().unwrap()
        } else {
            value_str.parse::<i64>().unwrap_or_else(|e| {
                panic!("could not parse value for '{var_name}': '{value_str}': {e}")
            })
        };

        assert!(
            predicate(value),
            "binding '{var_name} = {value}' failed validation in {smt2_file}"
        );
    }
}

/// Assert that ay returns "unsat" on the given file.
fn assert_unsat(smt2_file: &str) {
    let path = leetcode_dir().join(smt2_file);
    let (stdout, stderr, success) = run_ay(&path);

    // ay may return exit code 0 for both sat and unsat
    let first_line = stdout.lines().next().unwrap_or("");
    assert_eq!(
        first_line, "unsat",
        "expected unsat for {smt2_file}, got: {first_line}\nstderr: {stderr}\nsuccess: {success}"
    );
}

// ---------------------------------------------------------------------------
// LeetCode #1: Two Sum
// nums = [2, 7, 11, 15], target = 9
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_two_sum_sat() {
    assert_sat_with_model(
        "two_sum.smt2",
        &[
            // vi + vj = 9
            ("vi", &|v| v == 2 || v == 7),
            ("vj", &|v| v == 2 || v == 7),
        ],
    );
}

// ---------------------------------------------------------------------------
// LeetCode #322: Coin Change
// Denominations [10, 9, 1], target = 37, optimal = 4 coins
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_coin_change_sat() {
    assert_sat_with_model(
        "coin_change.smt2",
        &[
            ("total", &|v| v <= 4),
            ("c10", &|v| v >= 0),
            ("c9", &|v| v >= 0),
            ("c1", &|v| v >= 0),
        ],
    );
}

#[test]
#[timeout(10_000)]
fn test_leetcode_coin_change_optimal() {
    // 3 coins is not enough -> unsat proves 4 is optimal
    assert_unsat("coin_change_optimal.smt2");
}

// ---------------------------------------------------------------------------
// LeetCode #121: Best Time to Buy and Sell Stock
// prices = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8], optimal profit = 8
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_stock_profit_sat() {
    assert_sat_with_model(
        "stock_profit.smt2",
        &[
            ("profit", &|v| v >= 8),
            ("buy", &|v| (0..12).contains(&v)),
            ("sell", &|v| (0..12).contains(&v)),
        ],
    );
}

#[test]
#[timeout(10_000)]
fn test_leetcode_stock_profit_optimal() {
    // profit >= 9 is impossible -> unsat proves 8 is optimal
    assert_unsat("stock_profit_optimal.smt2");
}

// ---------------------------------------------------------------------------
// LeetCode #15 variant: Three Sum (a + b = c)
// Array = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8]
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_three_sum_sat() {
    assert_sat_with_model(
        "three_sum.smt2",
        &[
            // vi + vj = vk, all from the array
            ("vi", &|v| [1, 2, 3, 4, 5, 6, 8, 9].contains(&v)),
            ("vj", &|v| [1, 2, 3, 4, 5, 6, 8, 9].contains(&v)),
            ("vk", &|v| [1, 2, 3, 4, 5, 6, 8, 9].contains(&v)),
            // Distinct indices
            ("i", &|v| (0..12).contains(&v)),
            ("j", &|v| (0..12).contains(&v)),
            ("k", &|v| (0..12).contains(&v)),
        ],
    );
}

// ---------------------------------------------------------------------------
// LeetCode #84: Largest Rectangle in Histogram
// heights = [2, 1, 5, 6, 2, 3], optimal area = 10
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_largest_rectangle_sat() {
    assert_sat_with_model(
        "largest_rectangle_histogram.smt2",
        &[
            ("area", &|v| v >= 10),
            ("height", &|v| v >= 1),
            ("left", &|v| (0..=5).contains(&v)),
            ("right", &|v| (0..=5).contains(&v)),
        ],
    );
}

#[test]
#[timeout(10_000)]
fn test_leetcode_largest_rectangle_optimal() {
    // area >= 11 is impossible -> unsat proves 10 is optimal
    assert_unsat("largest_rectangle_optimal.smt2");
}

// ---------------------------------------------------------------------------
// LeetCode #51: N-Queens (N=5)
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_n_queens_5_sat() {
    assert_sat_with_model(
        "n_queens_5.smt2",
        &[
            ("q1", &|v| (1..=5).contains(&v)),
            ("q2", &|v| (1..=5).contains(&v)),
            ("q3", &|v| (1..=5).contains(&v)),
            ("q4", &|v| (1..=5).contains(&v)),
            ("q5", &|v| (1..=5).contains(&v)),
        ],
    );
}

// ---------------------------------------------------------------------------
// Graph Coloring: 6-node planar graph, 3 colors
// ---------------------------------------------------------------------------

#[test]
#[timeout(10_000)]
fn test_leetcode_graph_coloring_sat() {
    assert_sat_with_model(
        "graph_coloring.smt2",
        &[
            ("wa", &|v| (1..=3).contains(&v)),
            ("or_", &|v| (1..=3).contains(&v)),
            ("id", &|v| (1..=3).contains(&v)),
            ("nv", &|v| (1..=3).contains(&v)),
            ("ut", &|v| (1..=3).contains(&v)),
            ("az", &|v| (1..=3).contains(&v)),
        ],
    );
}
