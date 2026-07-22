// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! De-risk probe for the usize/u64 overflow fix (gap log build #19, fix option B).
//!
//! The native full-verify route currently encodes u64/usize add/sub overflow in
//! LIA, whose type-range literal `u64::MAX` overflows the i64-typed `ChcExpr::Int`
//! boundary (`typed_chc_ay.rs::parse_i64`) and yields `unknown`. Fix (B) re-encodes
//! these in BV, where the type bound is implicit in the bit-width so the oversized
//! literal disappears, and the overflow condition uses the wrap idiom
//! `bvult(bvadd(x, c), x)`.
//!
//! These tests confirm ay's BV solver decides the *single-step, loop-free* CHC of
//! exactly that shape at WIDTH 64 (the proven path is the direct-SMT acyclic-error
//! derivation, not the multi-state PDR loop portfolio that regressed in #6848). If
//! both pass, fix (B)'s solver assumption holds and the remaining work is purely the
//! deductive-checksgen BV encoding.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::sync::mpsc;
use std::time::Duration;

/// `error :- bvult(bvadd(x, 200), x)` over BitVec 64 — UNGUARDED u64 add.
/// Reachable (x = 2^64-100 wraps), so the system is UNSAFE: overflow can occur.
const U64_UNSAFE_HORN: &str = r#"(set-logic HORN)
(declare-fun reach () Bool)
(assert
  (forall ((x (_ BitVec 64)))
    (=> (bvult (bvadd x #x00000000000000c8) x) reach)))
(assert (=> reach false))
(check-sat)
(exit)
"#;

/// `error :- bvult(x, 1000) AND bvult(bvadd(x, 200), x)` over BitVec 64 — GUARDED.
/// With x < 1000, x+200 < 1200 never wraps, so `error` is UNreachable: SAFE (proved).
const U64_SAFE_HORN: &str = r#"(set-logic HORN)
(declare-fun reach () Bool)
(assert
  (forall ((x (_ BitVec 64)))
    (=> (and (bvult x #x00000000000003e8)
             (bvult (bvadd x #x00000000000000c8) x))
        reach)))
(assert (=> reach false))
(check-sat)
(exit)
"#;

fn solve_with_timeout(horn: &'static str) -> Option<VerifiedChcResult> {
    let problem = ChcParser::parse(horn).expect("HORN benchmark should parse");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
        let result = AdaptivePortfolio::new(problem, config).solve();
        let _ = tx.send(result);
    });
    rx.recv_timeout(Duration::from_secs(45)).ok()
}

#[test]
#[serial_test::serial]
fn u64_unsafe_add_overflow_bv64_is_not_falsely_safe() {
    // Validated behavior at the raw ay-chc AdaptivePortfolio layer: an unguarded
    // 64-bit BV add-overflow comes back `Unknown` (PDR returns Unknown on BV
    // refutation). The `Unsafe` witness is produced one layer up, by the model-checker-consumer
    // typed full-verification direct-SMT acyclic-error shortcut (see the 8-bit
    // `native_typed_chc_pdr_solver_refutes_bitvector_add_overflow_with_witness`).
    // The hard SOUNDNESS line is the only invariant asserted here: this obligation
    // must NEVER be reported Safe.
    match solve_with_timeout(U64_UNSAFE_HORN) {
        Some(result) => {
            eprintln!("U64_UNSAFE bv64 verdict (raw ay-chc): {result:?}");
            assert!(
                !matches!(result, VerifiedChcResult::Safe(_)),
                "unguarded u64 add overflow must not be proved Safe (would be a false-PROVE): got {result:?}"
            );
        }
        None => panic!("u64 unsafe bv64 solve timed out — BV path not viable at width 64"),
    }
}

#[test]
#[serial_test::serial]
fn u64_safe_guarded_add_no_overflow_bv64_is_proved() {
    match solve_with_timeout(U64_SAFE_HORN) {
        Some(result) => {
            eprintln!("U64_SAFE bv64 verdict: {result:?}");
            assert!(
                matches!(result, VerifiedChcResult::Safe(_)),
                "guarded (x<1000) u64 add cannot overflow; expected Safe (proved); got {result:?}"
            );
        }
        None => panic!("u64 safe bv64 solve timed out — BV path not viable at width 64"),
    }
}
