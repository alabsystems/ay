// Diophantine 2x2 fresh-variable-leak regression.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// The diophantine solver (ay-theories/lia/src/dioph) introduces fresh
// elimination variables for non-unit coefficients. Their determined values
// leaked into the Solved/Partial result maps with indices >= the original
// variable boundary, tripping a debug_assert in dioph_bridge.rs
// ("Solved value has out-of-range var index") and panicking debug builds on a
// 2x2 system with no unit coefficients (2x+3y=13, 4x+5y=23, SAT at x=2,y=3).
// The panic emitted no verdict, so on the no-proof-check subprocess backend the
// VC silently degraded to Unknown -- a common, simple integer shape that could
// never be proved.
//
// Fix: solve() strips fresh variables (index >= first_fresh_id) from the
// returned Solved/Partial map. Z3 answers `sat`; ay must answer `sat`, never
// panic or `unsat`.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> (String, bool) {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_LIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );
    let output = Command::new(ay_path)
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let panicked = stderr.contains("panicked");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let verdict = stdout
        .trim()
        .lines()
        .find(|l| !l.starts_with("c "))
        .unwrap_or("")
        .to_string();
    (verdict, panicked)
}

/// The 2x2 non-unit-coefficient system must solve to `sat` without panicking.
#[test]
#[timeout(60_000)]
fn dioph_2x2_no_unit_coeff_is_sat_not_panic() {
    let (verdict, panicked) = run_ay("dioph_2x2_no_unit_coeff.smt2");
    assert!(
        !panicked,
        "ay panicked on a 2x2 diophantine system (fresh-var leak regression); verdict={verdict:?}"
    );
    assert_ne!(
        verdict, "unsat",
        "Soundness regression: AY reported 'unsat' on a SAT QF_LIA system \
         (x=2, y=3; Z3 confirms SAT). Got: {verdict}"
    );
    assert_eq!(
        verdict, "sat",
        "Expected 'sat' on the 2x2 diophantine system, got: {verdict}"
    );
}
