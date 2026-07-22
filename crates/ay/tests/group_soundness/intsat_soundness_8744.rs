// IntSat probe soundness regression (#8744).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Regression test for the IntSat probe soundness smell (#8744). The IntSat
// probe in crates/ay-theories/lia/src/intsat_bridge.rs was returning UNSAT on
// partial DPLL states with a conflict clause blamed over ALL of
// `self.asserted`. The conflict was sound only by coincidence — if a bound
// reason ever included a literal not in `self.asserted` (e.g., from theory
// propagation), the claim would be unsound. This test guards the end-to-end
// behavior on the specific benchmark that exposed the smell: Z3 reports SAT
// in ~0.12s, so AY must never report UNSAT. `unknown` is acceptable (the
// probe bails out or the search times out); `sat` is acceptable (the full
// solver finds a model). `unsat` would be a soundness regression.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_LIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    // Use a tight timeout so `unknown` is the acceptable fall-through rather
    // than the test hanging.
    let output = Command::new(ay_path)
        .arg("-t:5000")
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8744: IntSat probe must not report UNSAT on `false_unsat_20var_bb.smt2`.
/// Z3 reports SAT; AY must report `sat` or `unknown` (never `unsat`).
#[test]
#[timeout(30_000)]
fn intsat_probe_never_reports_unsat_on_sat_20var_bb() {
    let result = run_ay("false_unsat_20var_bb.smt2");
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8744): AY reported 'unsat' on a SAT QF_LIA \
         instance (Z3 confirms SAT). Result: {result}"
    );
    // Sanity: it should be one of the standard values.
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on false_unsat_20var_bb.smt2: {result}"
    );
}
