// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Phase 1 regression test for #8717: CHC QF_BV completeness gaps.
//!
//! Two facets of #8717 are covered here:
//!
//! 1. **Sort-preservation fix (fast path, must-solve):** a BV+Int Horn
//!    loop where the BV state is unchanged between steps and the Int
//!    counter is bounded. AY solves this today via algebraic invariant
//!    synthesis. Before the Phase 1 fix the synthesizer hardcoded
//!    `ChcSort::Int` for the `{var}_next` post-state keys, which
//!    silently missed the BV post-state variable because `ChcVar`
//!    hashes on BOTH name and sort. This test exercises the fix path:
//!    the BV post-state update is now correctly keyed as `ChcSort::BV`
//!    and the substitution succeeds.
//!
//! 2. **Completeness floor (slow path, must-not-be-Unsafe):** a BV+Int
//!    Horn loop with `bvshl` state update (Z3 #1634 shape). Z3's Spacer
//!    solves it as `sat` (SAFE). AY currently times out; this assertion
//!    is a soundness floor (`Unsafe` = regression). Phase 2 (tracked in
//!    the development design notes) will gate algebraic
//!    synthesis on integer-only transitions and wire Spacer-style BV
//!    interpolation for the mixed case, which should flip this test
//!    into a `Safe`-required assertion.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::time::Duration;

/// Fast BV+Int Horn loop — BV state is identity-preserved, Int counter
/// bounded. Solved today by algebraic invariant synthesis.
///
/// This is the Phase 1 sort-preservation regression pin: the post-state
/// `x_next` variable must substitute correctly despite having
/// `ChcSort::BV` (not `ChcSort::Int`).
const BV_INT_IDENTITY_SAFE_8717: &str = r#"(set-logic HORN)

(declare-fun Inv ((_ BitVec 8) Int) Bool)

(assert
  (forall ((x (_ BitVec 8)) (i Int))
    (=> (and (= x (_ bv0 8)) (= i 0))
        (Inv x i))))

(assert
  (forall ((x (_ BitVec 8)) (i Int) (xp (_ BitVec 8)) (ip Int))
    (=> (and (Inv x i) (< i 5) (= ip (+ i 1)) (= xp x))
        (Inv xp ip))))

(assert
  (forall ((x (_ BitVec 8)) (i Int))
    (=> (and (Inv x i) (>= i 5) (not (= x (_ bv0 8))))
        false)))

(check-sat)
(exit)
"#;

/// Phase 1 sort-preservation: ay must solve a BV+Int Horn where the BV
/// post-state is identity and the Int counter is bounded.
///
/// The fix is in `algebraic_invariant::resolve_post_var_refs` /
/// `normalized_transition_expr`: post-state `{var}_next` keys now use
/// the real pre-state sort from `NormalizedSelfLoop::var_sorts` rather
/// than a hardcoded `ChcSort::Int`.
#[test]
#[serial_test::serial]
fn test_bv_int_identity_safe_8717_phase1_fix() {
    let problem = ChcParser::parse(BV_INT_IDENTITY_SAFE_8717)
        .expect("BV+Int identity Horn benchmark should parse");

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#8717 Phase 1: BV+Int identity Horn must solve Safe via algebraic \
         invariant synthesis. Result: {result:?}"
    );
}

/// Phase 2 gate regression (Z3 #1634 shape): BV+Int Horn with a `bvshl`
/// state update. The algebraic invariant synthesizer has no valid
/// polynomial closed form for this transition over Integers, so the
/// Phase 2 gate in `algebraic_invariant::bv_gate` must skip it — letting
/// the portfolio's remaining engines (PDR / IC3 / interpolation) try
/// within their own time budget instead of spinning on an invalid
/// recurrence.
///
/// Pre-gate (Phase 1 state): AY silently wasted the whole portfolio
/// budget inside `analyze_transition` / the downstream SMT refutation
/// of the malformed `x_next = x * 2^k` invariant, producing no result
/// within test-suite budgets.
///
/// Post-gate: AY bails from algebraic synthesis immediately and returns
/// `Unknown` (not `Safe`/`Unsafe`) within the configured portfolio time
/// budget. Phase 3 (BV MBP port) will flip this into a `Safe`-required
/// assertion.
const BV_INT_SHIFT_SAFE_8717_PHASE2: &str = r#"(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) Int) Bool)

(assert
  (forall ((x (_ BitVec 32)) (i Int))
    (=> (and (= x (_ bv0 32)) (= i 0))
        (Inv x i))))

(assert
  (forall ((x (_ BitVec 32)) (i Int) (xp (_ BitVec 32)) (ip Int))
    (=> (and (Inv x i)
             (< i 3)
             (= ip (+ i 1))
             (= xp (bvshl x (_ bv4 32))))
        (Inv xp ip))))

(assert
  (forall ((x (_ BitVec 32)) (i Int))
    (=> (and (Inv x i) (>= i 3) (not (= x (_ bv0 32))))
        false)))

(check-sat)
(exit)
"#;

/// Phase 2 gate test: a BV-heavy Horn whose transition relation contains a
/// `bvshl` update must NOT hang the algebraic invariant synthesizer. Under
/// the Phase 2 gate the synthesizer skips BV transitions entirely and the
/// portfolio returns `Unknown` within the configured time budget.
///
/// The regression being guarded is the synthesizer hanging past the
/// portfolio's configured budget. If this test regresses back to an
/// unbounded solve, the Phase 2 gate has been broken or bypassed.
#[test]
#[serial_test::serial]
fn test_bv_transition_skips_algebraic_invariant() {
    let problem = ChcParser::parse(BV_INT_SHIFT_SAFE_8717_PHASE2)
        .expect("BV+Int bvshl Horn benchmark should parse");

    // A tight 500ms portfolio budget keeps the test under its 5s
    // wall-clock ceiling even in debug builds (downstream PDR/BMC
    // engines add a fixed amount of startup overhead). The Phase 2 gate
    // ensures the algebraic synthesizer does not add to that time.
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_millis(500));
    let solver = AdaptivePortfolio::new(problem, config);

    let start = std::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();

    // The Phase 2 gate must keep the solve under the wall-clock budget.
    // Without it, algebraic synthesis would consume the full portfolio
    // budget producing an invalid recurrence, and the test would hit the
    // ntest 5s abort instead of returning here.
    assert!(
        elapsed < Duration::from_secs(5),
        "#8717 Phase 2: BV transition solve exceeded 5s wall clock (was {elapsed:?}). \
         The algebraic invariant gate may have regressed."
    );

    // Phase 2 only guarantees the algebraic synthesizer does not waste
    // time on a BV transition. Any outcome EXCEPT `Unsafe` is acceptable:
    //   - `Unknown`: the portfolio ran its non-algebraic engines within
    //     budget and could not conclude — Phase 3 (BV MBP port) will
    //     flip this to `Safe`.
    //   - `Safe`:    some other engine (PDR, interpolation, ...) solved
    //     the Horn clause after the algebraic gate stopped wasting time.
    //     This is BETTER than the Phase 2 target and should not be
    //     treated as a regression.
    //   - `Unsafe`:  SOUNDNESS regression — this benchmark is safe under
    //     BV semantics (`bvshl bv0 k = bv0` forever).
    assert!(
        !matches!(result, VerifiedChcResult::Unsafe(_)),
        "#8717 Phase 2: SOUNDNESS REGRESSION — BV+Int bvshl Horn must \
         not be reported Unsafe (it is safe under BV semantics). \
         Result: {result:?}"
    );
}
