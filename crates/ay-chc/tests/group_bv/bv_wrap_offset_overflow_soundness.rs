// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! P0 audit (model-checker-consumer parity wishlist 2026-07-17 item 2 / model-checker-consumer task #25):
//! PDR must not false-prove Safe on const-propped wrapping BV arithmetic.
//!
//! The attack shape: a wrapping `bvadd` counter whose UNSIGNED-INT abstraction
//! is overflow-free. PDR's Phase 1a/1b cube generalization weakens BV
//! equalities to Int-typed comparisons (`generalization_weakening.rs`)
//! justified by Int-semantics monotonicity oracles (`monotonicity.rs`), and
//! BV constants are read as unsigned integers (`extract_var_int_equality`).
//! If any of that chain were wrap-blind at the SEMANTIC level (i.e., the
//! mixed Int/BV queries built there were interpreted with non-wrapping
//! addition), the systems below would be proven Safe — but each has an error
//! state reachable ONLY via wrap.
//!
//! Audit result (2026-07-17): NOT constructible as a false-Safe today.
//! The mixed comparisons are given meaning via bv2nat (`smt/convert.rs`), so
//! the monotonicity queries contain the REAL wrapping `bvadd` transition and
//! the SMT check finds the wrap counterexample (`is_var_non_decreasing`
//! returns false / the weakened cube fails `is_inductive_blocking`). Every
//! widening is additionally SMT-re-checked, and the final
//! `verify_model`/`verify_model_fresh` pipeline re-proves each clause with
//! the same wrapping semantics — a lemma admitting the wrap would fail the
//! per-clause `body AND NOT head'` UNSAT check. These tests pin exactly that
//! behavior so a future wrap-blind shortcut (e.g., an Int-only fast path
//! that drops the BV transition constraint) turns them red.
//!
//! Measured verdicts at introduction (with the item-2 BV dual-confirmation
//! hardening active): the three wrap-reachable systems -> Unknown (sound;
//! standalone PDR does not unroll to the wrap depth, and crucially does NOT
//! admit the wrap-blind "monotone" invariant), the genuinely-safe residue
//! control -> Safe (no over-degradation).

use ay_chc::testing::pdr_solve_from_str;
use ay_chc::{PdrConfig, PdrResult};
use ntest::timeout;

fn verdict_name(r: &PdrResult) -> &'static str {
    match r {
        PdrResult::Safe(_) => "Safe",
        PdrResult::Unsafe(_) => "Unsafe",
        PdrResult::Unknown => "Unknown",
        _ => "Other",
    }
}

fn wrap_audit_config() -> PdrConfig {
    let mut config = PdrConfig::default();
    // Enough frames to reach the wrap depth of the shallow systems (15/19
    // steps) but bounded so the deep system terminates as Unknown.
    config.max_frames = 40;
    config.max_iterations = 2_000;
    config.max_obligations = 50_000;
    config.solve_timeout = Some(std::time::Duration::from_secs(30));
    config.verbose = false;
    config
}

/// Byte-offset-overflow archetype (the model-checker-consumer task #25 shape): offset
/// steps by 0x10; the error edge fires exactly when `bvadd` wraps
/// (`bvult (bvadd o #x10) o`). Unsigned-Int abstraction: o+16 > o always,
/// error "unreachable" => false Safe. BV truth: o reaches 0xF0 after 15
/// steps and wraps. Must NOT be Safe.
#[test]
#[timeout(120_000)]
fn test_bv_byte_offset_overflow_wrap_not_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((o (_ BitVec 8))) (=> (= o #x00) (inv o))))
(assert (forall ((o (_ BitVec 8))) (=> (inv o) (inv (bvadd o #x10)))))
(assert (forall ((o (_ BitVec 8)))
  (=> (and (inv o) (bvult (bvadd o #x10) o)) false)))
(check-sat)
"#;
    let result = pdr_solve_from_str(smt, wrap_audit_config()).expect("solve failed");
    eprintln!("byte_offset_overflow verdict: {}", verdict_name(&result));
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "SOUNDNESS (wishlist item 2 / task #25): byte-offset overflow IS reachable \
         (o=0xF0 after 15 steps, bvadd wraps); Safe would be a false proof from a \
         wrap-blind Int abstraction. Got Safe."
    );
}

/// Const-propped offset variant: init x=200, step +3; the error value x=1 is
/// reachable ONLY via wrap (200+3*19 = 257 = 0x01 mod 256). The unsigned-Int
/// abstraction {200+3k} never hits 1 and is monotone non-decreasing — the
/// exact situation where wrap-blind Phase 1a weakening (`x < 200` from
/// init-bound 200 with val 1 < min) would block a reachable state.
#[test]
#[timeout(120_000)]
fn test_bv_wrap_only_reachable_error_value_not_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #xC8) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (inv (bvadd x #x03)))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;
    let result = pdr_solve_from_str(smt, wrap_audit_config()).expect("solve failed");
    eprintln!("wrap_only_reachable verdict: {}", verdict_name(&result));
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "SOUNDNESS (wishlist item 2 / task #25): x=1 IS reachable via wrap \
         (200 + 3*19 = 257 = 1 mod 256); Safe would be a false proof. Got Safe."
    );
}

/// Deep-wrap variant: init 0, step +3, error x=1 — reachable only after 171
/// steps (3*171 = 513 = 1 mod 256), far beyond the frame budget. A correct
/// solver may answer Unsafe (if it can unroll that far) or Unknown, but a
/// Safe verdict within this budget can only come from a wrap-blind
/// generalization ("x stays a multiple of 3" / "x >= 0 monotone" are both
/// FALSE invariants under wrap).
#[test]
#[timeout(120_000)]
fn test_bv_deep_wrap_reachable_error_never_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (inv (bvadd x #x03)))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x01)) false)))
(check-sat)
"#;
    let result = pdr_solve_from_str(smt, wrap_audit_config()).expect("solve failed");
    eprintln!("deep_wrap verdict: {}", verdict_name(&result));
    assert!(
        !matches!(result, PdrResult::Safe(_)),
        "SOUNDNESS (wishlist item 2 / task #25): x=1 is reachable at depth 171 via \
         wrap; within this budget only Unsafe or Unknown are sound. Got Safe."
    );
}

/// Control (no over-degradation): the genuinely-Safe sibling — same wrapping
/// counter, but the error value 0x02 is NOT reachable (init 0, step +3: the
/// reachable set is the multiples of gcd(3,256)=1... all values ARE reachable
/// eventually, so use step +4: reachable set = multiples of 4, error 0x02
/// unreachable FOREVER, wrap included). PDR should be able to prove this Safe
/// with the invariant "x is a multiple of 4" or return Unknown — the test
/// only demands it does not claim Unsafe.
#[test]
#[timeout(120_000)]
fn test_bv_wrap_closed_residue_class_not_unsafe() {
    let smt = r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (inv (bvadd x #x04)))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #x02)) false)))
(check-sat)
"#;
    let result = pdr_solve_from_str(smt, wrap_audit_config()).expect("solve failed");
    eprintln!("closed_residue verdict: {}", verdict_name(&result));
    assert!(
        !matches!(result, PdrResult::Unsafe(_)),
        "x=2 is never reachable (reachable set is the multiples of 4, closed under \
         wrap); Unsafe would be wrong."
    );
}
