// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end regression test for #8734: BMC must not emit spurious `Unsafe`
//! on SAFE CHC problems whose predicate parameters contain `(Array Int Int)`.
//!
//! Before the fix:
//!   1. `simple_loop_array_portfolio_config` included a `BmcConfig::default()`
//!      engine, so the array-safe portfolio raced PDR against BMC.
//!   2. BMC's counterexample construction did not track array state; its
//!      underlying QF_AUFLIA + activation-literal queries went through a
//!      soundness gap in the SMT array theory (tracked in #8745). BMC would
//!      return `Unsafe` with a trace that dropped array arguments.
//!   3. The portfolio accepted BMC's `Unsafe` result, printing `unsat`
//!      (= UNSAFE) with a bogus counterexample on a safe benchmark.
//!
//! After the current fix set:
//!   - the SMT-layer array soundness bug (#8745) is fixed, so direct BMC no
//!     longer needs the old array-wide `Unsafe -> Unknown` downgrade; and
//!   - the array-safe adaptive portfolio can include BMC again because the
//!     underlying array-model soundness issue was fixed and the temporary
//!     adaptive-policy exclusion is no longer needed.
//!
//! This test exercises the full CLI path on both repro benchmarks cited in
//! the issue's acceptance criteria and asserts ay prints `sat` (= SAFE).

use ntest::timeout;
use std::process::Command;

fn run_chc(benchmark_rel_path: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    // `CARGO_MANIFEST_DIR` is `crates/ay`; benchmarks live at the repo root.
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let bench_path = std::path::Path::new(manifest_dir)
        .join("..")
        .join("..")
        .join(benchmark_rel_path);
    assert!(
        bench_path.exists(),
        "benchmark missing at {}",
        bench_path.display()
    );

    let output = Command::new(ay_path)
        .arg("--chc")
        .arg(&bench_path)
        .output()
        .expect("failed to run ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr);

    eprintln!("[{benchmark_rel_path}] exit: {:?}", output.status);
    eprintln!(
        "[{benchmark_rel_path}] stderr (tail): {}",
        stderr
            .lines()
            .rev()
            .take(5)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    );

    assert!(
        output.status.success(),
        "ay exited with {:?} on {benchmark_rel_path}",
        output.status,
    );
    stdout
}

fn first_line(stdout: &str) -> &str {
    stdout.lines().next().unwrap_or("").trim()
}

/// `test_array_int_pred.smt2` — the primary #8734 reproducer. SAFE (Z3: sat).
#[test]
#[timeout(60_000)]
fn test_chc_test_array_int_pred_is_sat_8734() {
    let stdout = run_chc("benchmarks/chc/test_array_int_pred.smt2");
    let line = first_line(&stdout);
    assert_ne!(
        line, "unsat",
        "#8734 regression: ay reported UNSAFE on a SAFE array CHC; output was:\n{stdout}",
    );
    assert_eq!(
        line, "sat",
        "Expected `sat` (SAFE) per #8734 acceptance criterion; got:\n{stdout}",
    );
}

/// `array_2param_int_8660.smt2` — companion reproducer from #8660 that must
/// still resolve to `sat` with array-safe BMC re-enabled.
#[test]
#[timeout(60_000)]
fn test_chc_array_2param_int_8660_is_sat_8734() {
    let stdout = run_chc("benchmarks/chc/array_2param_int_8660.smt2");
    let line = first_line(&stdout);
    assert_ne!(
        line, "unsat",
        "#8734 regression: ay reported UNSAFE on #8660 companion; output was:\n{stdout}",
    );
    assert_eq!(
        line, "sat",
        "Expected `sat` (SAFE) per #8734 acceptance criterion 2; got:\n{stdout}",
    );
}
