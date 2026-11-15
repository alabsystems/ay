// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Design §8 Rung 1 — `diff_lra`: random linear conjunctions over 3–8 Real
//! vars (bounds, sums, ITEs under Bool guards, strict/non-strict mixes,
//! disequalities) through the PRODUCTION router path on a warm Search-lane
//! context (200-query interleavings drawn from a shared conjunct pool) vs
//! legacy `check_sat` vs z3; the Real false-UNSAT counter is reported
//! separately (§7.3 (i)). Fixed sample size (CLI-owned convention: no
//! env-tunable count/seed here — bump the constants to widen the search
//! locally).

use crate::smt::session::harness::run_diff_lra;

/// Fixed sample size for [`random_lra_conjunctions_agree_with_legacy_and_z3`].
const DIFF_N: u64 = 1_200;
/// Fixed seed for [`random_lra_conjunctions_agree_with_legacy_and_z3`].
const DIFF_SEED: u64 = 2026;

#[test]
fn random_lra_conjunctions_agree_with_legacy_and_z3() {
    let n = DIFF_N;
    let seed = DIFF_SEED;
    let report = run_diff_lra(seed, n, true);
    eprintln!("[diff_lra] {}", report.summary());
    for d in report.disagreements.iter().take(5) {
        eprintln!("[diff_lra] DISAGREEMENT {d}");
    }
    for e in report.errors.iter().take(5) {
        eprintln!("[diff_lra] ERROR {e}");
    }
    assert!(
        report.errors.is_empty(),
        "harness errors: {:?}",
        report.errors
    );
    assert!(
        report.disagreements.is_empty(),
        "{} disagreements (first: {})",
        report.disagreements.len(),
        report.disagreements[0]
    );
    assert_eq!(report.real_false_unsat, 0, "Real false-UNSAT counter");
    assert_eq!(report.checks, n);
    let decided = report.session_sat + report.session_unsat;
    assert!(
        decided * 100 >= report.checks * 95,
        "session decided {decided}/{} (< 95 %): {}",
        report.checks,
        report.summary()
    );
    assert_eq!(
        report.unknown_unsupported, 0,
        "every generated query is eligible"
    );
    assert_eq!(report.unknown_poisoned, 0, "poison");
    assert_eq!(report.ext_full_reset_hits, 0, "ext_full_reset_hits");
}
