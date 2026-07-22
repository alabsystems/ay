// QF_AUFLIA storeinv_t3_pp_sf_ai soundness regression (#8804).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Issue #8804 covers false-SAT results on the classic
// Armando/Bonacina/Ranise/Schulz (PDPAR'05) `storeinv_t3_pp_sf_ai_*`
// QF_AUFLIA instances. They are declared UNSAT and independently confirmed
// UNSAT. The failure shape exercises array/EUF saturation across deep paired
// store chains, where ROW2-upward and extensionality must close a transitive
// equality loop.
//
// This test pins the three reported inputs to NOT return `sat`.
// `unsat` (correct) or `unknown` (completeness limit, soundness-
// preserving) are both acceptable. Any `sat` result on these
// benchmarks is a soundness bug and must never land.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smt/QF_AUFLIA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );

    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8804 reproducer (8 stores). Declared `:status unsat`. Z3 proves
/// UNSAT. AY must never answer `sat`; `unsat` or `unknown` are both
/// acceptable (unknown = completeness limit, not soundness).
#[test]
#[timeout(60_000)]
fn storeinv_8_is_not_sat_8804() {
    let result = run_ay("storeinv_t3_pp_sf_ai_00008_001.cvc.smt2", 30_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8804): AY reported 'sat' on a QF_AUFLIA \
         storeinv_t3_pp_sf_ai_00008_001 instance that Z3 proves UNSAT. \
         Expected 'unsat' or 'unknown'. Got: {result:?}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on storeinv_t3_pp_sf_ai_00008_001.cvc.smt2: {result:?}"
    );
}

/// #8804 reproducer (9 stores). Same invariants as the 8-store case.
#[test]
#[timeout(60_000)]
fn storeinv_9_is_not_sat_8804() {
    let result = run_ay("storeinv_t3_pp_sf_ai_00009_001.cvc.smt2", 30_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8804): AY reported 'sat' on a QF_AUFLIA \
         storeinv_t3_pp_sf_ai_00009_001 instance that Z3 proves UNSAT. \
         Expected 'unsat' or 'unknown'. Got: {result:?}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on storeinv_t3_pp_sf_ai_00009_001.cvc.smt2: {result:?}"
    );
}

/// #8804 reproducer (10 stores). Uses the same fail-closed policy as the
/// shorter store chains: `sat` is forbidden, while `unknown` is acceptable.
#[test]
#[timeout(60_000)]
fn storeinv_10_is_not_sat_8804() {
    let result = run_ay("storeinv_t3_pp_sf_ai_00010_001.cvc.smt2", 30_000);
    assert_ne!(
        result, "sat",
        "Soundness regression (#8804): AY reported 'sat' on a QF_AUFLIA \
         storeinv_t3_pp_sf_ai_00010_001 instance that Z3 proves UNSAT. \
         Expected 'unsat' or 'unknown'. Got: {result:?}"
    );
    assert!(
        result == "unsat" || result == "unknown",
        "Unexpected AY output on storeinv_t3_pp_sf_ai_00010_001.cvc.smt2: {result:?}"
    );
}
