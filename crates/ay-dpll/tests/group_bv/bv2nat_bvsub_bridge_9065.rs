// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV<->LIA bridge completeness gap 2 (#9065): `bvsub` under a `bv2nat` linkage.
//!
//! Once `len == (bv2nat k)` is asserted, the conservative BV<->LIA bridge used
//! to return `unknown (incomplete)` on ANY query whose term contained
//! `(bvsub k c)`, because the bridge never relates `bvsub` to an Int term —
//! even the trivially-valid `(bvult (bvsub k #x01) k)` given `(bvugt k #x04)`.
//!
//! The fix adds a SOUND relaxation fallback: when the bridge cannot find an
//! Int-side contradiction on a `bvsub`-containing query, it runs the eager BV
//! decision procedure (`solve_bv`) on the same roots. `solve_bv` encodes the
//! `bv2nat`/Int linkage to NO clauses, so it decides a pure-BV relaxation with
//! strictly fewer constraints; an UNSAT verdict on the relaxation entails UNSAT
//! of the original. The fallback promotes ONLY UNSAT — SAT/Unknown on the
//! relaxation stay `unknown` — so the cardinal soundness rule (never UNSAT for
//! a SAT query, never SAT for an UNSAT query) is preserved, and `bvsub` keeps
//! its exact mod-2^width wrapping semantics.

use ntest::timeout;

fn verdict(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

/// (a) The documented gap: a VALID `bvsub` goal under the `bv2nat` bridge.
/// `k >u 4` implies `k - 1 <u k` (no wrap), so the negated goal is UNSAT.
/// On the base revision this returned `unknown (incomplete)`.
#[test]
#[timeout(60_000)]
fn test_gap2_valid_bvsub_under_bv2nat_bridge_decided() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const len Int)
        (assert (= len (bv2nat k)))
        (assert (bvugt k (_ bv4 8)))
        (assert (not (bvult (bvsub k (_ bv1 8)) k)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "valid bvsub goal under bv2nat bridge must now be decided (UNSAT)"
    );
}

/// (a') / (d) The same goal WITHOUT the `bv2nat` linkage must be unchanged:
/// pure-BV, already decided `unsat` on the base revision.
#[test]
#[timeout(60_000)]
fn test_gap2_valid_bvsub_without_bridge_unchanged() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (assert (bvugt k (_ bv4 8)))
        (assert (not (bvult (bvsub k (_ bv1 8)) k)))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}

/// (b) A genuinely-FALSE `bvsub` query under the bridge: WITHOUT `k >u 0`,
/// `k = 0` wraps (`bvsub 0 1 = 0xFF`, so `0xFF <u 0` is false), hence the
/// negated goal is SATISFIABLE and the original `bvult` goal is NOT valid.
///
/// The cardinal rule requires we NEVER report this as `unsat`. The conservative
/// bridge promotes only UNSAT from the relaxation, so it correctly does not
/// claim validity here.
#[test]
#[timeout(60_000)]
fn test_gap2_false_bvsub_under_bridge_never_falsely_valid() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const len Int)
        (assert (= len (bv2nat k)))
        (assert (not (bvult (bvsub k (_ bv1 8)) k)))
        (check-sat)
    "#;
    let v = verdict(smt);
    assert_ne!(
        v, "unsat",
        "genuinely-invalid bvsub goal must NEVER be reported valid (unsat)"
    );
    // The sound relaxation cannot promote SAT (a dropped Int constraint could be
    // contradictory), so the bridge stays `unknown` here. Either non-unsat
    // answer is sound; pin the current behaviour for regression visibility.
    assert!(
        matches!(v.as_str(), "sat" | "unknown"),
        "expected sat or unknown for the invalid goal, got {v}"
    );
}

/// (d) The same FALSE query WITHOUT the bridge stays `sat` (pure-BV, unchanged).
#[test]
#[timeout(60_000)]
fn test_gap2_false_bvsub_without_bridge_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (assert (not (bvult (bvsub k (_ bv1 8)) k)))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat");
}

/// (c) Wrapping preserved: with `k = 0` the BV `bvsub` wraps to `2^8 - 1`, so
/// asserting `(bvsub k 1) != 0xFF` is contradictory. The fallback must refute
/// it (`unsat`) — a wrong wrap here would be a false UNSAT. Routed through the
/// bridge via the `bv2nat` linkage.
#[test]
#[timeout(60_000)]
fn test_gap2_bvsub_wrapping_violation_refuted_under_bridge() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const len Int)
        (assert (= len (bv2nat k)))
        (assert (= k (_ bv0 8)))
        (assert (not (= (bvsub k (_ bv1 8)) (_ bv255 8))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "k=0 forces (bvsub k 1) to wrap to 0xFF; requiring it != 0xFF is UNSAT"
    );
}

/// (c)/(d) The same wrapping-violation query WITHOUT the bridge must also be
/// `unsat` (pure-BV, unchanged) — both paths agree on wrapping semantics.
#[test]
#[timeout(60_000)]
fn test_gap2_bvsub_wrapping_violation_without_bridge() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (assert (= k (_ bv0 8)))
        (assert (not (= (bvsub k (_ bv1 8)) (_ bv255 8))))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}

/// A second VALID `bvsub` goal under the bridge, pinning a concrete value:
/// `k = 7` implies `(bvsub k 1) = 6`, so requiring it `!= 6` is UNSAT.
/// Exercises the relaxation fallback on the arithmetic-stall path.
#[test]
#[timeout(60_000)]
fn test_gap2_valid_bvsub_concrete_value_under_bridge() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const len Int)
        (assert (= len (bv2nat k)))
        (assert (= k (_ bv7 8)))
        (assert (not (= (bvsub k (_ bv1 8)) (_ bv6 8))))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}

/// Soundness guard: a `bvsub` query under the bridge that mixes a genuine
/// Int-side contradiction with a satisfiable BV part must come out `unsat`
/// via the bridge's own AUFLIA reasoning (NOT falsely SAT). `len = (bv2nat k)`
/// with `len > 255` is impossible for an 8-bit `k`.
#[test]
#[timeout(60_000)]
fn test_gap2_bvsub_int_side_contradiction_still_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const len Int)
        (assert (= len (bv2nat k)))
        (assert (> len 255))
        (assert (bvult (bvsub k (_ bv1 8)) k))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "Int-side contradiction (bv2nat of 8-bit k cannot exceed 255) must stay UNSAT"
    );
}
