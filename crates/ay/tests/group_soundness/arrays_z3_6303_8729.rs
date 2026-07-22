// Arrays soundness regression for Z3 #6303 / ay #8729.
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// #8729: ay returned `sat` on Z3#6303 byte-concat quantifier reproducer
// where the expected answer is `unsat`. Root cause (BV32 case): the
// post-solve guard in `quantifier_loop/result_mapping.rs::restore_assertions`
// trusted SAT whenever `ValidationStats.checked > 0`, but `checked`
// conflates independent verification with theory-delegated evidence
// (`delegated_checks`). When a quantifier assertion was skipped and the
// remaining ground disequality returned `Unknown+TERM_FLAG_ARRAY`, the
// observation pipeline emitted `delegated()` (because a bv_model was
// available), which incremented `checked` even though the BV/array
// theory solver had never seen the quantifier constraint.
//
// Fix: subtract `delegated_checks` from `checked` before counting
// evidence. After the fix, bv32 correctly returns `unknown` with
// reason `quantifier-ematching-exists`. bv8 still returns `sat` —
// that is a separate E-matching completeness problem (see
// `z3_open_bugs.rs::test_arrays_z3_6303_bv8_observed`).
//
// This file pins the soundness contract for bv32: the solver must
// never answer `sat` on this reproducer.

use ntest::timeout;
use std::process::Command;

fn repro_path(name: &str) -> String {
    format!(
        "{}/../ay-theories/arrays/tests/z3_soundness/{name}",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn run_ay(path: &str, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg("solve")
        .arg(path)
        .output()
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8729: Z3#6303 BV32 reproducer must not answer `sat`.
///
/// Z3 returns `unsat`; prior ay returned `sat` due to the
/// delegation-trust bug in `restore_assertions`. After the fix the
/// expected answer is `unknown` (reason: quantifier-ematching-exists)
/// until MBQI/E-matching completeness is extended to arrays.
#[test]
#[timeout(90_000)]
fn arrays_z3_6303_bv32_not_sat() {
    let path = repro_path("z3_6303_bv32.smt2");
    let result = run_ay(&path, 60_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8729): AY reported 'sat' on Z3#6303 \
         BV32 byte-concat reproducer. Z3 confirms UNSAT. Expected \
         'unsat' or 'unknown'. Result: {result}"
    );
}
