// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression: acyclic BV unsigned-remainder unreachable-arm safety must PROVE.
//!
//! This is the CHC that Trust's compiler emits for a provably-dead match arm:
//!
//! ```rust
//! pub fn lane_select(n: u32) -> u32 {
//!     match n % 3 { 0 => 100, 1 => 200, 2 => 300, _ => unreachable!() }
//! }
//! ```
//!
//! `error` is reachable only via `bb2`, which requires `bvurem n 3 ∉ {0,1,2}`.
//! That is UNSAT, so the system is SAFE (the `_` arm is dead).
//!
//! The acyclic-safe BMC certificate discharges each error branch via
//! `check_sat_with_executor_fallback`. The native DPLL(T) theory loop
//! restart-thrashes to its deadline on the bit-blasted `bvurem`, so unless the
//! ay-dpll Executor is reserved a budget (the fix this guards) the branch is
//! reported Unknown and the whole obligation degrades to a retained runtime
//! assertion instead of a static proof. Raw `bvurem n 3 >=u 3` is UNSAT in
//! ~100ms via ay-dpll, so the only failure mode here is budget starvation.

use ay_chc::{PdrConfig, VerifiedChcResult};
use std::time::Duration;

/// The exact Horn problem `compiler_consumer -Z deductive-verify-full` emits for `lane_select`
/// (captured via MODEL_CHECKER_CONSUMER_DUMP_CHC).
const LANE_SELECT_MODULO_CHC: &str = r#"(set-logic HORN)
(declare-var bb0_v0 (_ BitVec 32))
(declare-var bb1_thr_v0 (_ BitVec 32))
(declare-var bb2_thr_v0 (_ BitVec 32))
(declare-var bb3_thr_v0 (_ BitVec 32))
(declare-var bb4_thr_v0 (_ BitVec 32))
(declare-var bb5_thr_v0 (_ BitVec 32))
(declare-var lane_select_v18_0 (_ BitVec 32))
(declare-rel bb0 ((_ BitVec 32)))
(declare-rel bb1 ((_ BitVec 32)))
(declare-rel bb2 ((_ BitVec 32)))
(declare-rel bb3 ((_ BitVec 32)))
(declare-rel bb4 ((_ BitVec 32)))
(declare-rel bb5 ((_ BitVec 32)))
(declare-rel bb6 ())
(declare-rel error ())
(rule (=> true (bb0 bb0_v0)))
(rule (=> (and (bb0 bb0_v0) (not (= (= #x00000003 #x00000000) false))) error))
(rule (=> (bb0 bb0_v0) (bb1 bb0_v0)))
(rule (=> (and (bb1 bb1_thr_v0) (= #x00000003 #x00000000)) error))
(rule (=> (and (bb1 bb1_thr_v0) (= (bvurem bb1_thr_v0 #x00000003) #x00000000)) (bb5 bb1_thr_v0)))
(rule (=> (and (bb1 bb1_thr_v0) (= (bvurem bb1_thr_v0 #x00000003) #x00000001)) (bb4 bb1_thr_v0)))
(rule (=> (and (bb1 bb1_thr_v0) (= (bvurem bb1_thr_v0 #x00000003) #x00000002)) (bb3 bb1_thr_v0)))
(rule (=> (and (bb1 bb1_thr_v0) (and (not (= (bvurem bb1_thr_v0 #x00000003) #x00000000)) (not (= (bvurem bb1_thr_v0 #x00000003) #x00000001)) (not (= (bvurem bb1_thr_v0 #x00000003) #x00000002)))) (bb2 bb1_thr_v0)))
(rule (=> (and (bb2 bb2_thr_v0) (not false)) error))
(rule (=> (and (bb2 bb2_thr_v0) true) error))
(rule (=> (bb3 bb3_thr_v0) bb6))
(rule (=> (bb4 bb4_thr_v0) bb6))
(rule (=> (bb5 bb5_thr_v0) bb6))
(query error)"#;

#[test]
fn acyclic_bv_modulo_unreachable_arm_proves_safe() {
    // Mirror model-checker-consumer's proof-grade config (production + strict proofs).
    let mut config = PdrConfig::production(false).with_strict_proofs(true);
    config.solve_timeout = Some(Duration::from_secs(30));

    let run = ay_chc::engines::solve_pdr_proof_from_str(LANE_SELECT_MODULO_CHC, config)
        .expect("lane_select modulo CHC parses and runs");

    assert!(
        matches!(run.result(), VerifiedChcResult::Safe(_)),
        "acyclic BV-modulo unreachable arm (n%3 ∈ {{0,1,2}}) must prove SAFE \
         (Executor budget reserved for bvurem); got {:?}",
        run.result()
    );
}
