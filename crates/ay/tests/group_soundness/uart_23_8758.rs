// QF_LRA uart-23 soundness regression (#8758).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// #8758: `benchmarks/smtcomp/QF_LRA/uart-23.induction.cvc.smt2` historically
// returned a false UNSAT (Z3 reports `sat` in ~0.5s). The bug previously
// surfaced under #7575 (2026-03-22), #7577 (non-deterministic three-way LRA
// false-UNSAT family), and #8254 (six QF_LRA false-UNSAT soundness bugs,
// 2026-04-12). Each closure was followed by a regression because the root
// cause (LRA implied-bound reason chain mismatches cascading through the
// fixpoint propagation loop) sits at a heavily modified boundary between
// SAT-preprocessing reconstruction (#8397 chain) and LRA propagation
// (collect_interval_reasons / collect_row_reasons_dedup).
//
// Defense-in-depth now comes from three layers:
//   1. Implied-bound reason collection (f3c18be26, 9960cb8b6, 3d1763309) —
//      the root-cause fix, catches the underlying reason-chain mismatch.
//   2. Full-state soundness guard (15a19eafc) — release-build re-verifies
//      level-0 BCP theory conflicts and converts false UNSATs into unknown.
//   3. FINALIZE_SAT_FAIL poison (fc7323b87 on main; #8754) — downgrades
//      UNSAT to unknown after a failed SAT-model finalization.
//
// This test is the fourth and most specific layer: a named regression
// guard that asserts AY never prints `unsat` on uart-23. Either `sat`
// (the correct answer) or `unknown` (the guard engaged, or timeout)
// are both acceptable; `unsat` is a soundness regression and must fail
// the test.
//
// Related open issues (same family, likely shared root cause):
//   * #8511 — rand_*/tsp_rand_* LP benchmarks
//   * #8754 — simple_startup_6nodes.missing.induct
//   * #8758 — this benchmark
//
// Acceptance rationale for `unknown`: at the commit that introduced the
// fixpoint-propagation / full-state-guard / poison cascade, the solver
// is expected to bail to `unknown` rather than produce `unsat` on this
// instance. Restoring correct `sat` here is tracked under the parent
// LRA completeness issues (#8255, #8256, #8257, #8452) but must NOT
// reintroduce `unsat` — that is the soundness invariant guarded by
// this test.

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

/// #8758 primary reproducer: AY must never answer `unsat` on the induction
/// benchmark. Z3 answers `sat`; AY is allowed to answer `sat` (the correct
/// answer once LRA completeness is restored) or `unknown` (the
/// defense-in-depth guards engaged, or the solver timed out). `unsat` is a
/// soundness regression against the fixes that closed #7575 and #8254.
#[test]
#[timeout(90_000)]
fn uart_23_never_false_unsat_8758() {
    // Short internal timeout keeps the test fast. The current HEAD reliably
    // produces `unknown` in a few seconds once BCP / full-state guards kick
    // in; a 30s ceiling is plenty of headroom to allow `sat` to emerge if a
    // future LRA completeness fix restores it.
    let result = run_ay("uart-23.induction.cvc.smt2", 30_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8758): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}. See #7575, #7577, #8254 for prior closures; this \
         bug has regressed three times and MUST NOT be closed again without \
         a root-cause fix to the LRA implied-bound reason chain."
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on uart-23.induction.cvc.smt2: {result}"
    );
}
