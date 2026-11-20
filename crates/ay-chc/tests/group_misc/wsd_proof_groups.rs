// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CHC-COMP 2026 Workstream D (the development design notes at 9598c4206, §9) integration tests:
//! multi-group proof substrate: masks, path interpolants, fail-closed extraction, convert_path.
//!
//! Owner: WP-D1-P. The substrate is crate-internal; its API is unit-tested in
//! `interpolation/proof_groups_tests.rs`, the fail-closed extractor in
//! ay-dpll (`api/solving/interpolant_explicit_tests.rs`,
//! `tests/interpolation_lra_e2e.rs`) and `convert_path` in
//! `k_to_1_inductive/path.rs`. Here: end-to-end verdict locks on small
//! LRA-Lin transition systems through the public adaptive portfolio, whose
//! Real roster runs IMC — whose interpolants now come from the proof
//! substrate. Interpolants are candidates, never verdicts (INV-1): whatever
//! the substrate serves, a safe system must never be reported unsafe and an
//! unsafe one never safe.

#![allow(clippy::unwrap_used, clippy::panic)]

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::time::Duration;

fn solve(input: &str, label: &str) -> VerifiedChcResult {
    let problem = ChcParser::parse(input).unwrap_or_else(|e| panic!("parse {label}: {e}"));
    AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    )
    .solve()
}

/// `a <= 0` is 2-inductive (T swaps a and b), not 1-inductive: the IMC /
/// k→1 shape of Rung 1.
const SWAP_SAFE: &str = "\
(set-logic HORN)
(declare-fun inv (Real Real) Bool)
(assert (forall ((a Real) (b Real)) (=> (and (= a 0.0) (= b 0.0)) (inv a b))))
(assert (forall ((a Real) (b Real) (a1 Real) (b1 Real))
  (=> (and (inv a b) (= a1 b) (= b1 a)) (inv a1 b1))))
(assert (forall ((a Real) (b Real)) (=> (and (inv a b) (> a 0.0)) false)))
(check-sat)
";

/// Bool-moded Real counter (ITE transition): x and y grow by 1/2 only in
/// mode p, which toggles. Safe: the relational property `x = y` is
/// inductive although x is unbounded.
const MODED_SAFE: &str = "\
(set-logic HORN)
(declare-fun inv (Bool Real Real) Bool)
(assert (forall ((p Bool) (x Real) (y Real)) (=> (and p (= x 0.0) (= y 0.0)) (inv p x y))))
(assert (forall ((p Bool) (x Real) (y Real) (p1 Bool) (x1 Real) (y1 Real))
  (=> (and (inv p x y)
           (= p1 (not p))
           (= x1 (ite p (+ x 0.5) x))
           (= y1 (ite p (+ y 0.5) y)))
      (inv p1 x1 y1))))
(assert (forall ((p Bool) (x Real) (y Real)) (=> (and (inv p x y) (not (= x y))) false)))
(check-sat)
";

/// A Real counter that reaches the bad region after three steps.
const COUNTER_UNSAFE: &str = "\
(set-logic HORN)
(declare-fun inv (Real) Bool)
(assert (forall ((x Real)) (=> (= x 0.0) (inv x))))
(assert (forall ((x Real) (x1 Real)) (=> (and (inv x) (= x1 (+ x 0.5))) (inv x1))))
(assert (forall ((x Real)) (=> (and (inv x) (> x 1.2)) false)))
(check-sat)
";

#[test]
fn wsd_proof_groups_swap_is_safe() {
    let r = solve(SWAP_SAFE, "swap");
    assert!(matches!(r, VerifiedChcResult::Safe(_)), "swap: {r:?}");
}

#[test]
fn wsd_proof_groups_moded_counter_is_safe() {
    let r = solve(MODED_SAFE, "moded");
    assert!(
        !matches!(r, VerifiedChcResult::Unsafe(_)),
        "moded: a safe system must never be reported unsafe: {r:?}"
    );
}

#[test]
fn wsd_proof_groups_counter_is_unsafe() {
    let r = solve(COUNTER_UNSAFE, "counter");
    assert!(
        !matches!(r, VerifiedChcResult::Safe(_)),
        "counter: an unsafe system must never be reported safe: {r:?}"
    );
}
