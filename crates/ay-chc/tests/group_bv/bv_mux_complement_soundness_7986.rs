// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #7986: BV mk_mux complement optimization soundness.
//!
//! Root cause: ay-theories/bv/src/gates.rs `mk_mux` used XNOR(sel, b) instead
//! of XNOR(sel, a) when branches are complements (a = -b). This inverts the
//! mux output, causing the BV solver to return false-UNSAT on satisfiable
//! formulas involving `(ite (= #b1 (extract K K x)) bit_K (not bit_K))`.
//!
//! In CHC context, the BV solver's false-UNSAT on reachability queries causes
//! PDR/BMC to believe error states are unreachable, producing a false Safe
//! (PROOF) verdict on systems that are actually unsafe (CTREX).
//!
//! Fixed by: 44aafc14b (mk_xnor(sel, a) instead of mk_xnor(sel, b))
//! Guards against a false safety proof in `assert_hides_ub`.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::time::Duration;

/// Minimal BV CHC problem exercising the complement-branch mux pattern.
///
/// The system has one predicate `inv(x : BV8, b : Bool)` where `b` tracks
/// whether bit 0 of `x` is set. The transition uses `extract 0 0` to link
/// the Bool and BV state. The error condition checks that `b = true` implies
/// bit 0 of `x` is 1 — but the init clause sets `x = #x00` (bit 0 = 0) AND
/// `b = true`, which is immediately contradicted by the error check.
///
/// Actually, this system is UNSAFE because the initial state has x=#x00, b=true
/// and the query checks (inv(x,b) AND b AND (extract 0 0 x) = #b0) => false.
/// Since x=#x00 has bit 0 = 0 and b=true, the error is reachable at depth 0.
///
/// The mk_mux complement bug would cause the BV solver to incorrectly evaluate
/// the extract-based ITE, potentially making it think the error is unreachable.
const BV_MUX_COMPLEMENT_UNSAFE: &str = r#"(set-logic HORN)

(declare-fun inv ( (_ BitVec 8) Bool ) Bool)

; Init: x = 0, b = true (b does NOT match bit 0 of x — inconsistent state)
(assert
  (forall ( (x (_ BitVec 8)) (b Bool) )
    (=>
      (and (= x #x00) (= b true))
      (inv x b)
    )
  )
)

; Transition: x' = bvadd(x, 1), b' = ite(extract(0,0,x') = #b1, true, false)
; This is the complement-branch ITE pattern that triggers mk_mux optimization.
(assert
  (forall ( (x (_ BitVec 8)) (b Bool) (x2 (_ BitVec 8)) (b2 Bool) )
    (=>
      (and
        (inv x b)
        (= x2 (bvadd x #x01))
        (= b2 (= #b1 ((_ extract 0 0) x2)))
      )
      (inv x2 b2)
    )
  )
)

; Error: if b is true but bit 0 of x is 0, that's an error.
; Reachable at init: x=0x00 has bit 0 = 0, but b=true.
(assert
  (forall ( (x (_ BitVec 8)) (b Bool) )
    (=>
      (and
        (inv x b)
        b
        (= ((_ extract 0 0) x) #b0)
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

/// Soundness regression: BV complement-branch mux must NOT produce false Safe.
///
/// The system is UNSAFE (error reachable at init). If AY returns Safe,
/// the BV mk_mux complement optimization is broken (#7996 / #7986).
#[test]
#[serial_test::serial]
fn test_bv_mux_complement_unsafe_7986() {
    let problem =
        ChcParser::parse(BV_MUX_COMPLEMENT_UNSAFE).expect("BV mux complement CHC should parse");

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        !matches!(result, VerifiedChcResult::Safe(_)),
        "#7986: BV complement-branch mux system is UNSAFE (error reachable at init). \
         AY returned Safe — this indicates the mk_mux complement optimization bug \
         (XNOR with wrong operand) is causing false-Safe CHC results."
    );
}

/// Second pattern: extract-based ITE with explicit complement branches.
///
/// Uses `(ite (= #b1 (extract K K x)) bit_K (not bit_K))` — the exact
/// pattern from dualexecution/MCMPC QF_BV benchmarks that triggered #5512
/// and #7996. In CHC context, this pattern appears after BvToBool expansion
/// of pointer-width BV variables (model-checker-consumer encoding of assert_hides_ub).
const BV_EXTRACT_ITE_COMPLEMENT_UNSAFE: &str = r#"(set-logic HORN)

(declare-fun state ( (_ BitVec 8) Bool Bool ) Bool)

; Init: x = #xFF, b0 = false, b7 = true
; b0 should be true (bit 0 of #xFF is 1), but init says false => error
(assert
  (forall ( (x (_ BitVec 8)) (b0 Bool) (b7 Bool) )
    (=>
      (and (= x #xFF) (= b0 false) (= b7 true))
      (state x b0 b7)
    )
  )
)

; Transition: identity (loop back)
(assert
  (forall ( (x (_ BitVec 8)) (b0 Bool) (b7 Bool) )
    (=>
      (state x b0 b7)
      (state x b0 b7)
    )
  )
)

; Error: b0 must equal (extract 0 0 x) = #b1
; At init: x=#xFF so bit 0 = 1, but b0=false. So error is reachable.
(assert
  (forall ( (x (_ BitVec 8)) (b0 Bool) (b7 Bool) )
    (=>
      (and
        (state x b0 b7)
        (not (= b0 (= #b1 ((_ extract 0 0) x))))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;

/// Soundness: extract-ITE complement pattern must detect error.
///
/// Error is reachable because init sets b0=false while x=#xFF has bit 0 = 1.
/// The error condition checks b0 != (extract(0,0,x) = #b1), which is violated.
#[test]
#[serial_test::serial]
fn test_bv_extract_ite_complement_unsafe_7986() {
    let problem = ChcParser::parse(BV_EXTRACT_ITE_COMPLEMENT_UNSAFE)
        .expect("BV extract ITE complement CHC should parse");

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        !matches!(result, VerifiedChcResult::Safe(_)),
        "#7986: BV extract-ITE complement system is UNSAFE (b0 inconsistent with extract at init). \
         AY returned Safe — BV mk_mux complement bug causes false-Safe CHC results."
    );
}
