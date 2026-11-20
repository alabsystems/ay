// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CHC-COMP 2026 Workstream D (the development design notes at 9598c4206, §9) integration tests:
//! IMC budget-shaped retry, k->1 witness, source-aware validation; PDKind cancellation.
//!
//! Owner: WP-D1-E. The IMC retry and k→1 witness step are unit-tested next to
//! the engine (`imc/tests/wsd_retry_k1.rs`, they need its test seams); this
//! file drives the public API.

use ay_chc::{testing, CancellationToken, ChcParser, PdkindResult};
use ntest::timeout;
use std::time::{Duration, Instant};

/// (name, text, expected safe). S-reap (`tte_synchro.sm_clock_distance_strict_000`,
/// LRA-Lin) and the LIA-Lin loss `metros_4_e2_968_e3_931_000`: on both, a
/// cancelled PDKind kept interpolating (and ran its sanity BMC without a
/// token) for 21–36 s.
const INSTANCES: &[(&str, &str, bool)] = &[
    (
        "tte_synchro.sm_clock_distance_strict_000",
        include_str!("../fixtures/cancel_latency/tte_synchro.sm_clock_distance_strict_000.smt2"),
        false,
    ),
    (
        "metros_4_e2_968_e3_931_000",
        include_str!("../fixtures/cancel_latency/metros_4_e2_968_e3_931_000.smt2"),
        true,
    ),
];

/// "Within one query of cancel" (DESIGN §9): run bare, PDKind has only its
/// token — an SMT check already in flight is not interrupted (that is the
/// portfolio lane binding's job, measured by the lib test
/// `portfolio::tests::cancel_latency`), and PDKind's longest per-query cap is
/// `check_sat_10s`. Before the fix the post-cancel tail was 21–36 s.
const MAX_CANCEL_LATENCY: Duration = Duration::from_secs(12);

/// PDKind (no portfolio around it, so only its own token) returns within one
/// query when cancelled mid-run: the reachability loop and the sanity BMC
/// observe the token.
#[test]
#[timeout(120_000)]
fn pdkind_returns_promptly_after_mid_run_cancellation() {
    for (name, text, expected_safe) in INSTANCES {
        let problem = ChcParser::parse(text).expect("fixture parses");
        let token = CancellationToken::new();
        let solver_token = token.clone();
        let (tx, rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let result = testing::pdkind_solver_cancellation(problem, solver_token).solve();
            let _ = tx.send((Instant::now(), result));
        });
        if let Ok((_, result)) = rx.recv_timeout(Duration::from_secs(3)) {
            // Solved (or gave up) before the cancellation point: nothing to time.
            worker.join().expect("pdkind worker");
            let wrong = if *expected_safe {
                matches!(result, PdkindResult::Unsafe(_))
            } else {
                matches!(result, PdkindResult::Safe(_))
            };
            assert!(!wrong, "{name}: wrong PDKind verdict {result:?}");
            continue;
        }
        let cancelled_at = Instant::now();
        token.cancel();
        let (finished_at, result) = rx
            .recv_timeout(Duration::from_secs(45))
            .unwrap_or_else(|_| panic!("{name}: PDKind still running 45 s after cancellation"));
        worker.join().expect("pdkind worker");
        let latency = finished_at.saturating_duration_since(cancelled_at);
        assert!(
            latency <= MAX_CANCEL_LATENCY,
            "{name}: PDKind returned {latency:?} after cancellation (bound {MAX_CANCEL_LATENCY:?}), result {result:?}"
        );
    }
}
