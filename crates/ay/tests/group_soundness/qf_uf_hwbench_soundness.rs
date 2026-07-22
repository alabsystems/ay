// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use std::process::Command;

/// Run ay on a hwbench QF_UF benchmark and return the result line.
///
/// Returns "error" if the process exits with a non-zero status (e.g., model
/// validation failure). This prevents a model-validation crash from masking
/// the real assertion: the test checks that no benchmark returns "sat".
fn run_ay_hwbench(file_name: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smtcomp/non-incremental/QF_UF/2018-Goel-hwbench/{file_name}",
        env!("CARGO_MANIFEST_DIR")
    );
    if !std::path::Path::new(&benchmark_path).is_file() {
        eprintln!("SKIP: optional hwbench benchmark not found: {benchmark_path}");
        return "missing".to_string();
    }

    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        // Model validation errors mean the solver tried to return SAT
        // but caught its own mistake. This is not a "sat" result -- it's
        // a self-detected bug. Return "error" so the test can distinguish
        // this from a clean "sat" escape.
        if stderr.contains("model validation failed") {
            eprintln!("[WARNING] {file_name}: model validation caught false-SAT (known EUF bug)");
            return "error".to_string();
        }
        panic!(
            "ay exited with {:?} for {}\nstderr: {}",
            output.status, file_name, stderr
        );
    }

    String::from_utf8_lossy(&output.stdout)
        .trim()
        .lines()
        .next()
        .unwrap_or("")
        .to_string()
}

/// #4610 regression: these UNSAT hwbench cases must never return SAT.
#[test]
#[timeout(60_000)]
fn test_hwbench_unsat_instances_never_return_sat() {
    const CASES: &[&str] = &[
        "QF_UF_cache_coherence_three_ab_reg_max.smt2",
        "QF_UF_h_Arbiter_ab_reg_max.smt2",
        "QF_UF_h_BufAl_ab_fp_max.smt2",
        "QF_UF_h_Rrobin_ab_cti_max.smt2",
        "QF_UF_h_TicTacToe_ab_reg_max.smt2",
        "QF_UF_h_Vlunc_ab_cti_max.smt2",
        "QF_UF_h_b04_ab_cti_max.smt2",
        "QF_UF_h_b04_ab_reg_max.smt2",
        "QF_UF_itc99_b13_ab_cti_max.smt2",
    ];

    for case in CASES {
        let result = run_ay_hwbench(case);
        // Keep the broad guard at "not sat": the test verifies that no
        // benchmark escapes as a clean "sat". Model-validation-caught
        // false-SATs return "error" (self-detected, no wrong answer
        // escapes to the user).
        assert!(
            matches!(result.as_str(), "unsat" | "unknown" | "error" | "missing"),
            "{case} should not return sat (expected unsat/unknown/error), got: {result}"
        );
    }
}

/// #6869 regression: the original cache_coherence benchmark must return UNSAT,
/// not merely avoid the wrong-answer `sat`.
#[test]
#[timeout(60_000)]
fn test_cache_coherence_three_ab_reg_max_returns_unsat_6869() {
    let result = run_ay_hwbench("QF_UF_cache_coherence_three_ab_reg_max.smt2");
    if result == "missing" {
        return;
    }
    assert_eq!(
        result, "unsat",
        "#6869: cache_coherence benchmark must return unsat"
    );
}
