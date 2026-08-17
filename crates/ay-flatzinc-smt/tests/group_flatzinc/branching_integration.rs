// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Integration tests for the branching search solver (FD-track compliance).
//
// These tests verify that `solve_branching()` correctly follows search
// annotations (VarChoice, ValChoice) via backtracking search using one-shot
// ay invocations.
//
// Part of #322 (search heuristics), #273 (MiniZinc entry).

use ay_flatzinc_smt::{solve_branching, translate, SolverConfig, TranslationResult};

use super::common;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

fn make_config() -> SolverConfig {
    SolverConfig {
        timeout_ms: Some(30_000),
        all_solutions: false,
        global_deadline: None,
    }
}

/// Solve a satisfaction problem with branching and verify the output.
///
/// Two variables x in [1,3], y in [1,3] with x != y.
/// Search annotation: input_order + indomain_min.
/// Branching should assign x=1, y=2 (first valid combo with min values).
#[test]
fn branching_satisfy_input_order_indomain_min() {
    let config = make_config();

    let fzn = "\
        var 1..3: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve :: int_search([x, y], input_order, indomain_min, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 1, "should find exactly one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    // Output must contain the solution separator
    assert!(
        output_str.contains("----------"),
        "output must contain solution separator, got: {output_str}"
    );
    // With input_order + indomain_min, branching tries x=1 first, then y=1
    // (fails due to x!=y), then y=2 (succeeds). So x=1, y=2.
    assert!(
        output_str.contains("x = 1") && output_str.contains("y = 2"),
        "input_order+indomain_min should find x=1, y=2, got: {output_str}"
    );
}

/// Verify that indomain_max produces a different solution than indomain_min.
///
/// Same model but with indomain_max: branching should try x=3 first, y=3
/// (fails), y=2 (succeeds). So x=3, y=2.
#[test]
fn branching_satisfy_input_order_indomain_max() {
    let config = make_config();

    let fzn = "\
        var 1..3: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve :: int_search([x, y], input_order, indomain_max, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 1, "should find exactly one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    assert!(
        output_str.contains("----------"),
        "output must contain solution separator"
    );
    // With indomain_max, branching tries x=3 first, then y=3 (fails), y=2 (succeeds).
    assert!(
        output_str.contains("x = 3") && output_str.contains("y = 2"),
        "input_order+indomain_max should find x=3, y=2, got: {output_str}"
    );
}

/// Verify first_fail variable ordering: smaller domain is tried first.
///
/// x in [1,5] (domain size 5), y in [1,2] (domain size 2).
/// With first_fail, y should be branched on first (smaller domain).
/// With indomain_min: y=1, then x=1 (but x != y), so x=2.
#[test]
fn branching_satisfy_first_fail_ordering() {
    let config = make_config();

    let fzn = "\
        var 1..5: x :: output_var;\n\
        var 1..2: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve :: int_search([x, y], first_fail, indomain_min, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 1, "should find exactly one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    // first_fail picks y first (domain size 2 < 5), assigns y=1.
    // Then x: tries x=1 (fails, x!=y), x=2 (succeeds).
    assert!(
        output_str.contains("y = 1"),
        "first_fail should branch on y first (smaller domain), got: {output_str}"
    );
    assert!(
        output_str.contains("x = 2"),
        "after y=1, x should be 2 (first valid with indomain_min), got: {output_str}"
    );
}

/// Verify branching optimization finds the optimal solution.
///
/// Minimize x where x in [1,5], y in [1,5], x + y >= 4.
/// The optimal solution is x=1 (with y=3 or similar).
#[test]
fn branching_optimize_minimize() {
    let config = make_config();

    let fzn = "\
        var 1..5: x :: output_var;\n\
        var 1..5: y :: output_var;\n\
        constraint int_lin_le([1, 1], [x, y], 6);\n\
        constraint int_lin_le([-1, -1], [x, y], -4);\n\
        solve :: int_search([x, y], input_order, indomain_min, complete) minimize x;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert!(solutions >= 1, "should find at least one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    // Should prove optimality
    assert!(
        output_str.contains("=========="),
        "optimization should prove optimality, got: {output_str}"
    );
    // The last solution before ========== should have x=1
    // (minimum x satisfying x+y >= 4 with y <= 5 is x=1, y=3)
    let lines: Vec<&str> = output_str.lines().collect();
    // Find the last solution line containing x =
    let last_x = lines
        .iter()
        .rev()
        .find(|l| l.contains("x = "))
        .expect("must have x assignment");
    assert!(
        last_x.contains("x = 1"),
        "optimal x should be 1, got: {last_x}"
    );
}

/// Verify indomain_split uses binary split branching (split_branch path).
///
/// x in [1,8], y in [1,8], x + y = 9.
/// indomain_split bisects the domain: first tries x<=4, then x<=2, etc.
/// This exercises the split_branch buffer truncation logic (see #326).
#[test]
fn branching_satisfy_indomain_split() {
    let config = make_config();

    let fzn = "\
        var 1..8: x :: output_var;\n\
        var 1..8: y :: output_var;\n\
        constraint int_lin_eq([1, 1], [x, y], 9);\n\
        solve :: int_search([x, y], input_order, indomain_split, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 1, "should find exactly one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    assert!(
        output_str.contains("----------"),
        "output must contain solution separator, got: {output_str}"
    );
    // indomain_split bisects: tries x<=4 first. Within that, x<=2, then x<=1.
    // So x=1 is the first tried leaf. With x=1, y=8 satisfies x+y=9.
    assert!(
        output_str.contains("x = 1") && output_str.contains("y = 8"),
        "indomain_split should find x=1 (left-biased bisection), y=8, got: {output_str}"
    );
}

/// Verify indomain_reverse_split tries the upper half first.
///
/// Same model as above but with indomain_reverse_split.
/// Should try x>4 first, then x>6, then x>7, landing on x=8.
#[test]
fn branching_satisfy_indomain_reverse_split() {
    let config = make_config();

    let fzn = "\
        var 1..8: x :: output_var;\n\
        var 1..8: y :: output_var;\n\
        constraint int_lin_eq([1, 1], [x, y], 9);\n\
        solve :: int_search([x, y], input_order, indomain_reverse_split, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 1, "should find exactly one solution");
    let output_str = String::from_utf8(output).expect("valid utf8");
    assert!(
        output_str.contains("----------"),
        "output must contain solution separator, got: {output_str}"
    );
    // indomain_reverse_split bisects from the right: tries x>4 first, then x>6, x>7.
    // So x=8 is the first tried leaf. With x=8, y=1 satisfies x+y=9.
    assert!(
        output_str.contains("x = 8") && output_str.contains("y = 1"),
        "indomain_reverse_split should find x=8 (right-biased bisection), y=1, got: {output_str}"
    );
}

/// Verify split_branch handles unsatisfiable with full backtracking.
///
/// x in [1,4], y in [1,4], x + y = 10 (impossible since max is 8).
/// split_branch must exhaust all branches and report unsatisfiable.
/// This tests that buffer truncation is correct across full backtrack exhaustion.
#[test]
fn branching_split_unsatisfiable() {
    let config = make_config();

    let fzn = "\
        var 1..4: x :: output_var;\n\
        var 1..4: y :: output_var;\n\
        constraint int_lin_eq([1, 1], [x, y], 10);\n\
        solve :: int_search([x, y], input_order, indomain_split, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 0, "should find no solutions (max x+y = 8 < 10)");
    let output_str = String::from_utf8(output).expect("valid utf8");
    assert!(
        output_str.contains("=====UNSATISFIABLE====="),
        "should report unsatisfiable, got: {output_str}"
    );
}

/// Verify branching handles unsatisfiable problems correctly.
///
/// x in [1,2], y in [1,2], x != y, x > 2 (impossible).
#[test]
fn branching_unsatisfiable() {
    let config = make_config();

    let fzn = "\
        var 1..2: x :: output_var;\n\
        var 1..2: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        constraint int_gt(x, 2);\n\
        solve :: int_search([x, y], input_order, indomain_min, complete) satisfy;\n";

    let result = translate_fzn(fzn);
    let mut output = Vec::new();
    let solutions = solve_branching(&result, &config, &mut output).expect("solve failed");

    assert_eq!(solutions, 0, "should find no solutions");
    let output_str = String::from_utf8(output).expect("valid utf8");
    assert!(
        output_str.contains("=====UNSATISFIABLE====="),
        "should report unsatisfiable, got: {output_str}"
    );
}

// ---------------------------------------------------------------------------
// Real MiniZinc Challenge 2024 benchmark tests (FD-track / CP-track)
// ---------------------------------------------------------------------------

/// Helper: construct path to a compiled FZN benchmark (CP track).
fn benchmark_cp_path(relative: &str) -> std::path::PathBuf {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR required");
    // Try ay repo benchmarks first
    let ay_path = std::path::PathBuf::from(&manifest)
        .join("../../benchmarks/minizinc/compiled-fzn-cp/2024")
        .join(relative);
    if ay_path.exists() {
        return ay_path;
    }
    // Fallback to win-all repo (sibling checkout)
    let home = std::env::var("HOME").unwrap_or_default();
    std::path::PathBuf::from(home)
        .join("win-all-software-proof-competitions/benchmarks/minizinc/compiled-fzn-cp/2024")
        .join(relative)
}

include!("branching_integration/benchmark_models.rs");

// ---------------------------------------------------------------------------
// IncrementalSolver protocol test — detects ay pipe buffering bug
// ---------------------------------------------------------------------------

/// Read stdout lines until SYNC marker or timeout, via background thread.
///
/// Returns `Ok(lines)` if marker found, `Err(())` on timeout.
fn read_pipe_with_timeout(
    stdout: std::io::BufReader<std::process::ChildStdout>,
    marker: &str,
    timeout_secs: u64,
) -> Result<Vec<String>, ()> {
    use std::io::BufRead;
    use std::sync::mpsc;
    use std::time::Duration;

    let marker_owned = marker.to_string();
    let marker_quoted = format!("\"{marker}\"");
    let (tx, rx) = mpsc::channel();

    std::thread::spawn(move || {
        let mut reader = stdout;
        let mut lines = Vec::new();
        loop {
            let mut line = String::new();
            match reader.read_line(&mut line) {
                Ok(0) => break,
                Ok(_) => {
                    let trimmed = line.trim().to_string();
                    let is_sync = trimmed == marker_owned || trimmed == marker_quoted;
                    lines.push(trimmed);
                    if is_sync {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
        let _ = tx.send(lines);
    });

    rx.recv_timeout(Duration::from_secs(timeout_secs))
        .map_err(|_| ())
}

/// Verify ay responds to check-sat via stdin/stdout pipes (incremental mode).
///
/// The IncrementalSolver relies on ay flushing stdout after each command
/// response. If ay fully buffers stdout on pipes, incremental solving hangs.
///
/// Part of #328, #273.
#[test]
fn incremental_solver_ay_pipe_responds() {
    use std::io::{BufReader, BufWriter, Write};
    use std::process::Stdio;

    let _ay_guard = common::ay_process_guard();
    let mut child = common::ay_command()
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn ay");

    let mut stdin = BufWriter::new(child.stdin.take().unwrap());
    let stdout = BufReader::new(child.stdout.take().unwrap());

    let script = "(declare-const x Int)\n\
                  (assert (>= x 1))\n(assert (<= x 3))\n\
                  (push 1)\n(assert (= x 1))\n\
                  (check-sat)\n(echo \"SYNC_TEST\")\n";
    stdin.write_all(script.as_bytes()).unwrap();
    stdin.flush().unwrap();

    let result = read_pipe_with_timeout(stdout, "SYNC_TEST", 10);

    let _ = stdin.write_all(b"(exit)\n");
    drop(stdin);
    let _ = child.kill();
    let _ = child.wait();

    match result {
        Ok(lines) => {
            assert!(!lines.is_empty(), "ay should produce output over pipes");
            assert!(
                lines.iter().any(|l| l == "sat"),
                "ay should return 'sat', got: {lines:?}"
            );
        }
        Err(()) => panic!(
            "TIMEOUT: ay did not respond within 10s over pipes. ay fully buffers \
             stdout on pipes. IncrementalSolver blocked until ay flushes. See #328."
        ),
    }
}
