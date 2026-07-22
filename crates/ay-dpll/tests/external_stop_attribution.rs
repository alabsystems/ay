// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests (#quantifier-determinism, defect 2): an EXTERNAL stop
//! (caller watchdog interrupt flag, or an expired solve deadline) that lands
//! mid-NIA must surface as `Unknown(Interrupted)` / `Unknown(Timeout)` — NOT
//! as `Unknown(UnsupportedArithmetic)`.
//!
//! Before the fix, `refine_unsupported_fragment_unknown_reason` stamped
//! `UnsupportedArithmetic` over the truncated solve's generic Incomplete/None
//! reason whenever the formula contained `div`/`mod`, so callers misclassified
//! a load-dependent truncation as a permanent capability gap (this exact
//! mis-attribution made a ported deductive-checks nonlinear case look like a pin
//! regression). `finalize_unknown_diagnostics` deliberately never overrides
//! UnsupportedArithmetic once stamped, so the external-stop test must happen
//! before stamping — these tests pin that end-to-end.
//!
//! VERDICT-NEUTRAL: the attribution fix only reclassifies `unknown`; it never
//! manufactures a definitive verdict. This probe may now independently reach
//! `sat` because the NIA lane has grown stronger, so only its `unknown` branches
//! exercise the reason-attribution regression.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_dpll::UnknownReason;
use ntest::timeout;

/// QF_NIA semiprime factoring with a `div` atom. Current descendants may either
/// complete this as SAT or stop fail-closed as
/// Unknown(Incomplete/UnsupportedArithmetic); it still takes long enough for a
/// short deadline or early watchdog flip to exercise external-stop attribution
/// while keeping the ladder cheap.
const NIA_DIV_QUERY: &str = r#"
    (set-logic QF_NIA)
    (declare-fun p () Int)
    (declare-fun q () Int)
    (declare-fun w () Int)
    (assert (> p 1))
    (assert (> q 1))
    (assert (< p 1000))
    (assert (< q 1000))
    (assert (= (* p q) 611161))
    (assert (= w (div p 7)))
    (check-sat)
"#;

fn run_with_timeout(budget: Duration) -> (Vec<String>, Duration, Option<UnknownReason>) {
    let commands = ay_frontend::parse(NIA_DIV_QUERY).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    exec.set_timeout(Some(budget));
    let start = Instant::now();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    (outputs, start.elapsed(), exec.unknown_reason())
}

/// Deadline variant: a ladder of short budgets must observe at least one
/// end-to-end `Timeout`, never convert every truncated solve into a capability
/// gap. A completed solve may now return `sat` because the NIA lane has grown
/// stronger since this regression was introduced; a still-incomplete solve may
/// retain `UnsupportedArithmetic` or a generic `Incomplete` when it finishes
/// before its deadline.
///
/// Do not infer that the deadline fired from `elapsed > budget`: `elapsed` is
/// sampled after `execute_all` returns, so final result formatting/scheduling
/// can cross the wall after the solver already finalized a genuine result. The
/// executor's outward reason is the authoritative observation. Unit tests on
/// `refine_unsupported_fragment_unknown_reason` separately pin the exact
/// expired-deadline precedence branch.
#[test]
#[timeout(60000)]
fn expired_deadline_mid_nia_is_timeout_not_unsupported_arithmetic() {
    let mut saw_timeout = false;
    for budget_ms in [1u64, 2, 3, 4, 6, 8] {
        let budget = Duration::from_millis(budget_ms);
        let (outputs, elapsed, reason) = run_with_timeout(budget);
        match outputs.as_slice() {
            [output] if output == "unknown" => match reason {
                Some(UnknownReason::Timeout) => saw_timeout = true,
                Some(UnknownReason::UnsupportedArithmetic) | Some(UnknownReason::Incomplete) => {}
                other => panic!(
                    "budget={budget_ms}ms elapsed={elapsed:?}: incomplete NIA \
                     must be attributed Timeout, UnsupportedArithmetic, or Incomplete, \
                     got {other:?}"
                ),
            },
            [output] if output == "sat" => assert_eq!(
                reason, None,
                "budget={budget_ms}ms elapsed={elapsed:?}: a definitive SAT \
                 result must not retain an unknown reason"
            ),
            other => panic!(
                "budget={budget_ms}ms elapsed={elapsed:?}: satisfiable NIA \
                 deadline probe returned unexpected outputs {other:?}"
            ),
        }
    }
    assert!(
        saw_timeout,
        "calibration: the positive-budget ladder observed no Timeout; enlarge \
         NIA_DIV_QUERY so it still exercises a deadline during solver work"
    );
}

/// Interrupt variant: a watchdog thread flips the caller interrupt flag
/// shortly after the solve starts (the deductive-checks watchdog pattern). Whenever
/// the flip demonstrably landed while the solve still had meaningful work
/// left (elapsed comfortably beyond the flip), the reason must be
/// Interrupted. Falls back to a pre-set flag (guaranteed Interrupted via the
/// entry abort) if the machine solves too fast for a reliable mid-solve flip;
/// a SAT completion before the flip is likewise inconclusive and retried, so
/// the test never flakes as this NIA lane grows faster.
#[test]
#[timeout(60000)]
fn interrupt_mid_nia_is_interrupted_not_unsupported_arithmetic() {
    const FLIP_DELAY: Duration = Duration::from_millis(1);
    // Ordering margin: the flip must precede the solve tail (where the
    // attribution refinement runs) by a comfortable distance.
    const MARGIN: Duration = Duration::from_millis(3);

    for _attempt in 0..3 {
        let commands = ay_frontend::parse(NIA_DIV_QUERY).expect("valid SMT-LIB input");
        let mut exec = ay_dpll::Executor::new();
        let flag = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(flag.clone());
        let watchdog = {
            let flag = Arc::clone(&flag);
            std::thread::spawn(move || {
                std::thread::sleep(FLIP_DELAY);
                flag.store(true, Ordering::Relaxed);
            })
        };
        let start = Instant::now();
        let outputs = exec.execute_all(&commands).expect("execution succeeds");
        let elapsed = start.elapsed();
        watchdog.join().expect("watchdog thread joins");

        match outputs.as_slice() {
            [output] if output == "unknown" => {
                if elapsed > FLIP_DELAY + MARGIN {
                    assert_eq!(
                        exec.unknown_reason(),
                        Some(UnknownReason::Interrupted),
                        "elapsed={elapsed:?}: an interrupt landing mid-NIA must be \
                         attributed Interrupted, not a capability gap"
                    );
                    return;
                }
            }
            [output] if output == "sat" => assert_eq!(
                exec.unknown_reason(),
                None,
                "elapsed={elapsed:?}: a SAT completion before the watchdog flip \
                 must not retain an unknown reason"
            ),
            other => panic!(
                "elapsed={elapsed:?}: satisfiable NIA interrupt probe returned \
                 unexpected outputs {other:?}"
            ),
        }
        // Solve finished SAT or too close to the flip to trust the ordering —
        // retry, then use the deterministic pre-interrupted fallback.
    }

    // Fast-machine fallback: with the flag set before the call, the abort is
    // guaranteed external and must be attributed Interrupted.
    let commands = ay_frontend::parse(NIA_DIV_QUERY).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    exec.set_interrupt(Arc::new(AtomicBool::new(true)));
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    assert_eq!(outputs, vec!["unknown"]);
    assert_eq!(
        exec.unknown_reason(),
        Some(UnknownReason::Interrupted),
        "a pre-interrupted solve must be attributed Interrupted"
    );
}
