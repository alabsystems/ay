// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! SOUNDNESS pins for the BV128 `Ord::min`/`max` → `Inst::Select` bridge model
//! (external-codegen-ir-bridge `lower.rs`, BV128 task #57).
//!
//! The bridge lowers an integer `a.max(b)` / `a.min(b)` to an EXACT
//! `ite(cmp(a, b), a, b)` (`Inst::Select` over an `Inst::ICmp`), where `cmp` is
//! signed (`bvsge`/`bvsle`) for signed operands and unsigned (`bvuge`/`bvule`)
//! for unsigned — the SIGNEDNESS IS TYPE-DIRECTED. A wrong signedness (e.g. an
//! unsigned compare on `i128`) or a swapped `Select` arm would let the verifier
//! PROVE A FALSE ARITHMETIC FACT, which is catastrophic. These tests drive the
//! EXACT encoded formula through ay's real CHC solver at WIDTH 128 and pin:
//!
//!   * KNOWN-FALSE properties must NEVER come back `Safe` (a `Safe` here would be
//!     a false-PROVE — the hard soundness line). At this raw ay-chc layer a BV
//!     refutation may surface as `Unknown` rather than `Unsafe` (see the sibling
//!     `u64_overflow_bv_derisk`), so the invariant asserted is `!Safe`.
//!   * KNOWN-TRUE properties must come back `Safe` (the faithful model is
//!     accepted, not merely fail-closed).
//!   * The SIGNEDNESS catcher (test D) shows that the WRONG (unsigned) model of a
//!     signed `max` DOES break a signed lower-bound property — proving the
//!     type-directed signedness in the bridge is load-bearing, not cosmetic.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use std::sync::mpsc;
use std::time::Duration;

// 128-bit hex literals (32 hex digits).
const ZERO: &str = "#x00000000000000000000000000000000";
const ONE: &str = "#x00000000000000000000000000000001";

/// Solve a loop-free single-relation HORN benchmark on a worker thread with a
/// hard wall-clock cap (matches `u64_overflow_bv_derisk::solve_with_timeout`).
fn solve(horn: String) -> Option<VerifiedChcResult> {
    let problem = ChcParser::parse(&horn).expect("HORN benchmark should parse");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
        let _ = tx.send(AdaptivePortfolio::new(problem, config).solve());
    });
    rx.recv_timeout(Duration::from_secs(45)).ok()
}

/// Wrap a violation condition (the NEGATION of the property under test) into a
/// HORN system whose error relation `reach` is derivable exactly when the
/// property is VIOLATED. `vars` is the SMT-LIB binder list.
fn horn(vars: &str, violation: &str) -> String {
    format!(
        "(set-logic HORN)\n\
         (declare-fun reach () Bool)\n\
         (assert (forall ({vars}) (=> {violation} reach)))\n\
         (assert (=> reach false))\n\
         (check-sat)\n(exit)\n"
    )
}

fn assert_not_safe(name: &str, horn: String) {
    match solve(horn) {
        Some(result) => {
            eprintln!("{name}: verdict {result:?}");
            assert!(
                !matches!(result, VerifiedChcResult::Safe(_)),
                "{name}: a KNOWN-FALSE property was proved Safe — FALSE PROOF: {result:?}"
            );
        }
        None => panic!("{name}: solve timed out"),
    }
}

fn assert_safe(name: &str, horn: String) {
    match solve(horn) {
        Some(result) => {
            eprintln!("{name}: verdict {result:?}");
            assert!(
                matches!(result, VerifiedChcResult::Safe(_)),
                "{name}: a KNOWN-TRUE property was not proved Safe: {result:?}"
            );
        }
        None => panic!("{name}: solve timed out"),
    }
}

// ---- KNOWN-FALSE — must NOT prove (must NOT be Safe) ----

/// (A) Swapped-arm / order catcher: signed `max(a,b) == a` is FALSE when `b > a`.
/// Model = the exact signed lowering `ite(bvsge(a,b), a, b)`.
#[test]
#[serial_test::serial]
fn signed_max_eq_first_arg_is_not_provable() {
    let model = "(ite (bvsge a b) a b)";
    let violation = format!("(not (= {model} a))");
    assert_not_safe(
        "signed_max_eq_first_arg",
        horn("(a (_ BitVec 128)) (b (_ BitVec 128))", &violation),
    );
}

/// (D) SIGNEDNESS catcher: the WRONG unsigned model `ite(bvuge(a,0), a, 0)` of a
/// SIGNED `max(a, 0)` collapses to `a` (everything is `bvuge 0`), so the signed
/// lower bound `result >=s 0` is VIOLATED at `a = -1`. This must NOT be Safe —
/// it demonstrates that a mis-signed compare in the bridge WOULD be a false
/// proof, so the type-directed signedness is load-bearing.
#[test]
#[serial_test::serial]
fn wrong_unsigned_model_of_signed_max_breaks_lower_bound() {
    let wrong_model = format!("(ite (bvuge a {ZERO}) a {ZERO})");
    let violation = format!("(bvslt {wrong_model} {ZERO})");
    assert_not_safe(
        "wrong_unsigned_model_of_signed_max",
        horn("(a (_ BitVec 128))", &violation),
    );
}

/// (E) 128-bit modular / truncation catcher: `wrapping_add(a, 1) != 0` is FALSE
/// at `a == u128::MAX` (wraps to 0). A 64-bit-truncated encoding would falsely
/// prove `!= 0`.
#[test]
#[serial_test::serial]
fn u128_wrapping_add_one_ne_zero_is_not_provable() {
    let violation = format!("(= (bvadd a {ONE}) {ZERO})");
    assert_not_safe(
        "u128_wrapping_add_one_ne_zero",
        horn("(a (_ BitVec 128))", &violation),
    );
}

/// (F) Modular catcher: `wrapping_add(a, 1) > a` is FALSE at `a == u128::MAX`. A
/// non-modular (natural-number) encoding would falsely prove `>`.
#[test]
#[serial_test::serial]
fn u128_wrapping_add_one_gt_is_not_provable() {
    let violation = format!("(bvule (bvadd a {ONE}) a)");
    assert_not_safe(
        "u128_wrapping_add_one_gt",
        horn("(a (_ BitVec 128))", &violation),
    );
}

// ---- KNOWN-TRUE — must prove (must be Safe) ----

/// (B) Unsigned `max(a,b) >= a && >= b` is TRUE. Model = the exact unsigned
/// lowering `ite(bvuge(a,b), a, b)` — the `range_i128`/`u128` `.max` case.
#[test]
#[serial_test::serial]
fn unsigned_max_dominates_both_args_is_proved() {
    let model = "(ite (bvuge a b) a b)";
    let violation = format!("(or (bvult {model} a) (bvult {model} b))");
    assert_safe(
        "unsigned_max_dominates_both_args",
        horn("(a (_ BitVec 128)) (b (_ BitVec 128))", &violation),
    );
}

/// (C) Signed `max(a, 0) >= 0` is TRUE — and provable ONLY with a SIGNED compare
/// (`bvsge`). This is the positive counterpart of test D: the CORRECT signed
/// model `ite(bvsge(a,0), a, 0)` proves the signed lower bound.
#[test]
#[serial_test::serial]
fn signed_max_with_zero_lower_bound_is_proved() {
    let model = format!("(ite (bvsge a {ZERO}) a {ZERO})");
    let violation = format!("(bvslt {model} {ZERO})");
    assert_safe(
        "signed_max_with_zero_lower_bound",
        horn("(a (_ BitVec 128))", &violation),
    );
}

/// (G) Unsigned `min(a,b) <= a && <= b` is TRUE. Model = the exact unsigned
/// lowering `ite(bvule(a,b), a, b)`.
#[test]
#[serial_test::serial]
fn unsigned_min_dominated_by_both_args_is_proved() {
    let model = "(ite (bvule a b) a b)";
    let violation = format!("(or (bvugt {model} a) (bvugt {model} b))");
    assert_safe(
        "unsigned_min_dominated_by_both_args",
        horn("(a (_ BitVec 128)) (b (_ BitVec 128))", &violation),
    );
}
