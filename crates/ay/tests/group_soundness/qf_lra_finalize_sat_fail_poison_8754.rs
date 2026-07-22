// QF_LRA FINALIZE_SAT_FAIL poison regression (#8754).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// #8754: The solve loop used to print `FINALIZE_SAT_FAIL: BUG: original clause
// N/M unsatisfied ...` to stderr when the internal SAT model failed to
// satisfy the original ledger, but then continued searching and could return
// a later `unsat` from learned clauses that were derived against a corrupted
// state. On `simple_startup_6nodes.missing.induct.smt2` this produced a false
// UNSAT (Z3 reports SAT in ~150 ms).
//
// The fix makes `finalize_sat_fail_count` sticky across the entire solve call
// and downgrades any subsequent UNSAT to `unknown` with a loud
// `FINALIZE_SAT_FAIL_POISON: ...` diagnostic. This test guards that contract:
// on the benchmark that originally reproduced the bug, AY must never print
// `unsat`. `sat` or `unknown` are both acceptable.

use ntest::timeout;
use std::process::Command;

fn run_ay(smt_file: &str, timeout_ms: u64) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}/../../benchmarks/smtcomp/QF_LRA/{}",
        env!("CARGO_MANIFEST_DIR"),
        smt_file
    );
    if !std::path::Path::new(&benchmark_path).is_file() {
        eprintln!("SKIP: optional QF_LRA benchmark not found: {benchmark_path}");
        return "unknown".to_string();
    }

    let output = Command::new(ay_path)
        .arg(format!("-t:{timeout_ms}"))
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8754 primary reproducer: AY must never answer `unsat` on the induction
/// benchmark. Z3 answers `sat`; AY is allowed to answer `sat` or `unknown`
/// (the latter once the FINALIZE_SAT_FAIL poison engages), but `unsat`
/// is a soundness regression.
#[test]
#[timeout(120_000)]
fn finalize_sat_fail_poison_never_false_unsat_on_simple_startup_6nodes() {
    let result = run_ay("simple_startup_6nodes.missing.induct.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8754): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on simple_startup_6nodes.missing.induct.smt2: \
         {result}"
    );
}

// NOTE: `rand_70_300_1155482584_11.lp.smt2` is a separate soundness bug
// (#8511 family) that is NOT caught by the FINALIZE_SAT_FAIL poison fix —
// the internal SAT solver returns UNSAT without ever producing an invalid
// model for finalize_sat_model to reject. A regression test for that
// benchmark belongs with the root-cause fix, not this one.
