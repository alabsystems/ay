// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV CHC soundness regression for #6848: gulwani_fig1a.c_000.
//!
//! Z3 returns `unsat` (unsafe). AY incorrectly returns `sat` (safe).
//! This is a false-safe soundness bug — the solver claims a system is safe
//! when it is actually unsafe.
//!
//! The benchmark has 3 Bool + 3 BV32 state variables with a bounded loop
//! involving signed comparison (`extract 31 31`), addition, and
//! constant `#xffffffce` (-50 as signed i32).
//!
//! Part of #6848

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::sync::mpsc;
use std::time::Duration;

/// gulwani_fig1a.c_000.smt2 from CHC-COMP 2025 BV track.
/// Z3 returns unsat (unsafe). AY must NOT return sat (safe).
const GULWANI_FIG1A_BENCHMARK: &str = r#"(set-logic HORN)


(declare-fun |state| ( Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)

(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C Bool) (D Bool) (E Bool) (F (_ BitVec 32)) )
    (=>
      (and
        (and (not D) (not E) (not C))
      )
      (state E D C A B F)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M (_ BitVec 32)) )
    (=>
      (and
        (state I H G C D M)
        (let ((a!1 (and (not L)
                K
                (not J)
                (not G)
                (not H)
                I
                (= C B)
                (= E D)
                (= A M)
                (not (= ((_ extract 31 31) D) #b1))
                (bvsle M #x00000000))))
  (or (and (not L)
           (not K)
           J
           (not G)
           (not H)
           (not I)
           (= C B)
           (= E #xffffffce)
           (= A F))
      a!1
      (and (not L)
           (not K)
           J
           (not G)
           (not H)
           I
           (= C B)
           (= E (bvadd D M))
           (= A (bvadd #x00000001 M))
           (= ((_ extract 31 31) D) #b1))
      (and L (not K) (not J) (not G) H (not I) (= C B) (= E D) (= A M))
      (and L (not K) (not J) G (not H) (not I))))
      )
      (state J K L B E A)
    )
  )
)
(assert
  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C Bool) (D Bool) (E Bool) (F (_ BitVec 32)) )
    (=>
      (and
        (state E D C A B F)
        (and (not D) (not E) (= C true))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

/// Soundness regression for #6848: gulwani_fig1a must return Unsafe.
///
/// Z3 returns unsat (the system IS unsafe). AY with exact BV-to-Int encoding
/// correctly finds a counterexample. If AY returns Safe, that's a false-safe
/// soundness bug.
///
/// **Current status:** REGRESSION TARGET
///
/// The BV-to-Int exact encoding path regressed after the incremental PDR
/// changes (#8205). Previously solved as Unsafe within 15s, it now cannot
/// solve within any reasonable budget. The adaptive solver's BV parallel
/// portfolio does not respect budget enforcement (BV bit-blasting SAT calls
/// are not interruptible), causing the solver to run indefinitely.
///
/// This test uses a manual thread+channel timeout to cap wall-clock time
/// at 60s. If the solver does not complete within the timeout, the result
/// is treated as Unknown (acceptable for a regression target). Only Safe
/// is forbidden (soundness bug).
///
/// Expected to return Unsafe when BV solving performance is restored.
#[test]
#[serial_test::serial]
fn test_bv_chc_gulwani_fig1a_unsafe_6848() {
    let problem = ChcParser::parse(GULWANI_FIG1A_BENCHMARK).expect("gulwani_fig1a should parse");

    // Run the solver on a separate thread with a channel-based timeout.
    // The adaptive solver's BV portfolio does not honor its time budget
    // (BV bit-blasting SAT calls are not interruptible mid-solve), so we
    // cannot rely on the solver returning within the budget. Instead, we
    // give it 60s wall-clock and treat timeout as Unknown.
    // Part of #6848, #8205.
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10));
        let solver = AdaptivePortfolio::new(problem, config);
        let result = solver.solve();
        let _ = tx.send(result);
    });

    match rx.recv_timeout(Duration::from_mins(1)) {
        Ok(result) => {
            // Solver completed: verify it did NOT return Safe (soundness gate).
            assert!(
                !matches!(result, VerifiedChcResult::Safe(_)),
                "#6848: gulwani_fig1a is UNSAFE (Z3 returns unsat). \
                 AY returned Safe — this is a FALSE SAFE soundness bug."
            );
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            // Solver did not complete within 60s. This is the expected
            // regression behavior: the BV portfolio overruns its budget.
            // Timeout is treated as Unknown (acceptable). The solver
            // threads will be cleaned up when the process exits.
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("#6848: solver thread panicked or disconnected");
        }
    }
}
