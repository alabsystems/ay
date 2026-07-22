// QF_LRA stale reason conflict regression (#8764).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// #8764: `build_conflict_with_farkas()` used to flatten bound reasons into a
// theory conflict without re-checking that those reason atoms were still live
// in `self.asserted`. When backtracking retracted a bound reason between row
// infeasibility detection and conflict construction, AY could emit a stale
// conflict and return a false `unsat` on SAT QF_LRA benchmarks. The fix adds
// a release-mode stale-reason guard and degrades such conflicts to `unknown`.
// These regressions guard that contract: on the original reproducers, AY must
// never print `unsat`. `sat` or `unknown` are both acceptable.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

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
        .output_timeout(Duration::from_secs(115))
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    stdout.trim().lines().next().unwrap_or("").to_string()
}

/// #8764 reproducer: AY must never answer `unsat` on this random LP-family
/// benchmark. Z3 answers `sat`; AY is allowed to answer `sat` or `unknown`,
/// but `unsat` is a soundness regression.
#[test]
#[timeout(120_000)]
fn stale_reason_never_false_unsat_on_rand_70_300_4() {
    let result = run_ay("rand_70_300_1155482584_4.lp.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8764): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on rand_70_300_1155482584_4.lp.smt2: {result}"
    );
}

/// #8764 reproducer: AY must never answer `unsat` on this random LP-family
/// benchmark. Z3 answers `sat`; AY is allowed to answer `sat` or `unknown`,
/// but `unsat` is a soundness regression.
#[test]
#[timeout(120_000)]
fn stale_reason_never_false_unsat_on_rand_70_300_11() {
    let result = run_ay("rand_70_300_1155482584_11.lp.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8764): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on rand_70_300_1155482584_11.lp.smt2: {result}"
    );
}

/// #8764 reproducer: AY must never answer `unsat` on this random LP-family
/// benchmark. Z3 answers `sat`; AY is allowed to answer `sat` or `unknown`,
/// but `unsat` is a soundness regression.
#[test]
#[timeout(120_000)]
fn stale_reason_never_false_unsat_on_tsp_rand_70_300_7() {
    let result = run_ay("tsp_rand_70_300_1155482584_7.lp.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8764): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on tsp_rand_70_300_1155482584_7.lp.smt2: {result}"
    );
}

/// #8764 reproducer (hhk2008.c.i_3_3_2.bpl_8): AY must never answer `unsat`
/// on this Boogie-derived QF_LRA benchmark. Z3 answers `sat`; AY is allowed
/// to answer `sat` or `unknown`, but `unsat` is a soundness regression.
///
/// This case was observed to intermittently trip the false-UNSAT path prior
/// to the `build_conflict_with_farkas` stale-reason guard landing (commits
/// `d264e18b9`, `973bd0b8f`). Included here to lock the 4th acceptance-
/// criterion benchmark under regression coverage alongside the 3
/// `rand_70_300` / `tsp_rand_70_300` LP-family reproducers.
#[test]
#[timeout(120_000)]
fn stale_reason_never_false_unsat_on_hhk2008_3_3_2_bpl_8() {
    let result = run_ay("_hhk2008.c.i_3_3_2.bpl_8.smt2", 60_000);
    assert_ne!(
        result, "unsat",
        "Soundness regression (#8764): AY reported 'unsat' on a SAT QF_LRA \
         instance (Z3 confirms SAT). Expected 'sat' or 'unknown'. \
         Result: {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Unexpected AY output on _hhk2008.c.i_3_3_2.bpl_8.smt2: {result}"
    );
}
