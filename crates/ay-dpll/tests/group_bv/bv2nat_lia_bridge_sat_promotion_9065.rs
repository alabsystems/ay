// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV<->LIA bridge SAT promotion under a structural realizability guard
//! (#9065 / B2 PART 2).
//!
//! `solve_bv_lia_bridge` used to return `unknown (incomplete)` for the SAT
//! case, bypassing model validation — so a genuine-SAT Route-A query like
//! `(= L (bv2nat k))` (L Int, k BitVec occurring ONLY inside `bv2nat`) was
//! over-rejected to `unknown` end-to-end.
//!
//! PART 2 promotes that SAT branch to a real `sat` IFF BOTH:
//!   (a) the candidate AUFLIA model validates against the original roots, AND
//!   (b) EVERY BitVec variable occurs SOLELY as the direct argument of a
//!       `bv2nat`/`int2bv` bridge (never under `bvadd`/`bvult`/`concat`/
//!       `extract`/a BV `=`/…).
//! Under (b) the range-checked opaque `bv2nat` value `v` in `[0, 2^w)` is
//! realizable by the witness `x = int2bv_w(v)` with no competing BV constraint.
//!
//! CARDINAL RULE: these tests focus on the false-SAT hazard — a query whose BV
//! var has even one un-bridged occurrence must STAY `unknown` (never `sat`),
//! and a genuinely-UNSAT query must STAY `unsat`.

use ntest::timeout;

fn verdict(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

// ===========================================================================
// (a) PROMOTE: bridge-only, model-validating SAT queries -> sat (was unknown).
// ===========================================================================

/// The canonical Route-A companion: `L = bv2nat(k)`, `k` occurs ONLY inside
/// `bv2nat(k)`. Genuinely SAT (e.g. k = 0, L = 0); was `unknown` before PART 2.
#[test]
#[timeout(60_000)]
fn test_promote_basic_length_companion() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "bridge-only (= L (bv2nat k)) is genuinely SAT and must promote"
    );
}

/// Bridge-only with an in-range Int pin: `L = bv2nat(k)` and `L = 5`. Realized
/// by `k = int2bv_8(5) = #x05`.
#[test]
#[timeout(60_000)]
fn test_promote_in_range_int_pin() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= L 5))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "L=5 is in [0,256): realizable, must promote"
    );
}

/// Bridge-only with an in-range bound: `0 <= L < 10` and `L = bv2nat(k)`.
#[test]
#[timeout(60_000)]
fn test_promote_in_range_bounds() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (>= L 0))
        (assert (< L 10))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat");
}

/// Two distinct BV vars, each ONLY under `bv2nat`, combined in pure LIA:
/// `S = bv2nat(k) + bv2nat(m)`. Each opaque value is independently witnessable,
/// so this is bridge-only and SAT.
#[test]
#[timeout(60_000)]
fn test_promote_two_bridged_vars_sum() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const m (_ BitVec 8))
        (declare-const S Int)
        (assert (= S (+ (bv2nat k) (bv2nat m))))
        (assert (= S 12))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat");
}

/// `bv2nat(int2bv(8, s))` congruence shape — int2bv permitted as a bv2nat
/// argument (its value is determined by the Int source `s`). Bridge-only, SAT.
#[test]
#[timeout(60_000)]
fn test_promote_int2bv_under_bv2nat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const s Int)
        (declare-const L Int)
        (assert (= L (bv2nat ((_ int2bv 8) s))))
        (assert (= L 7))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "sat");
}

// ===========================================================================
// (b) PROMOTE-IF-VALIDATED vs DO-NOT-PROMOTE.
//
//     Original policy (bridge-only guard): a BV var with ANY un-bridged
//     occurrence stays `unknown`, conservatively avoiding a false SAT.
//
//     #overflow-mod / Piece 2 refines this: when every BitVec LEAF var has a
//     `bv2nat(var)` companion valued in the AUFLIA model, the leaves are
//     MATERIALIZED (`var = int2bv_W(bv2nat(var))`) and `validate_model`
//     recomputes the whole query from concrete bits. A model that genuinely
//     satisfies the ORIGINAL query then promotes to `sat`; a decoupled/spurious
//     one is rejected back to `unknown`. Each query below IS satisfiable, so the
//     validated promotion yields the CORRECT `sat` (never a false SAT — see the
//     `_rejects_*` soundness tests in bv2nat_add_sub_modular_bridge.rs and the
//     UNSAT-stays-UNSAT section (c) here). A leaf with NO companion (concat /
//     extract / a bare `k = m`) is still not materializable, so those stay
//     `unknown` — the conservative path is retained exactly where validation
//     cannot certify a witness.
// ===========================================================================

/// `k` under `bvult`: materialize `k` from its `bv2nat(k)` companion and
/// validate — the query is SAT (e.g. k = 0), so it promotes to a checked `sat`.
#[test]
#[timeout(60_000)]
fn test_no_promote_under_bvult() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (bvult k (_ bv5 8)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "k under bvult with a bv2nat(k) companion: materialized witness validates (SAT)"
    );
}

/// `k` under `bvadd`: the modular bridge introduces `bv2nat(k)`, so `k`
/// materializes and the SAT witness (k = 0, L = 1) validates.
#[test]
#[timeout(60_000)]
fn test_no_promote_under_bvadd() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat (bvadd k (_ bv1 8)))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "bvadd under bv2nat: materialized witness validates (SAT)"
    );
}

/// `k` under `concat`: must NOT promote.
#[test]
#[timeout(60_000)]
fn test_no_promote_under_concat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat (concat k (_ bv0 8)))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unknown",
        "concat under bv2nat: must NOT promote"
    );
}

/// `k` under `extract`: like the `bvadd` case above, the slice link
/// (`#bv2nat-extract-link`) relates `bv2nat(k[3:0])` to `bv2nat(k)`, so `k`
/// materializes and the SAT witness (k = #x00, L = 0) validates.
///
/// This row asserted `unknown` while the slice floated free of its source. That
/// was never the true answer — the query is trivially satisfiable — it was the
/// promotion guard declining a model it could not realize. The guard's real job
/// is refusing a FALSE `sat`, and that is unchanged: the published `sat` here is
/// a witness the independent model gate confirmed against the original roots.
#[test]
#[timeout(60_000)]
fn test_no_promote_under_extract() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat ((_ extract 3 0) k))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "extract under bv2nat: materialized witness validates (SAT)"
    );
}

/// `k` equated to another BV (`k = m`, a BitVec `=`): must NOT promote.
#[test]
#[timeout(60_000)]
fn test_no_promote_bv_equality() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const m (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= k m))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unknown",
        "k = m (BitVec equality) is an un-bridged occurrence: must NOT promote"
    );
}

/// Two `bv2nat` of `k` PLUS a `bvand` occurrence: `k` has a `bv2nat(k)`
/// companion, so it materializes; the witness (k = 0, L = 0, M = 0) validates
/// (`bvand(0,15) = 0`), a checked `sat`.
#[test]
#[timeout(60_000)]
fn test_no_promote_two_bv2nat_plus_bvand() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (declare-const M Int)
        (assert (= L (+ (bv2nat k) (bv2nat k))))
        (assert (= M (bv2nat (bvand k (_ bv15 8)))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "bvand under bv2nat with a bv2nat(k) companion: materialized witness validates (SAT)"
    );
}

/// `k` under `bvslt` (signed compare): `k` materializes from `bv2nat(k)`; the
/// SAT witness (k = 0, signed 0 < 5) validates.
#[test]
#[timeout(60_000)]
fn test_no_promote_under_bvslt() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (bvslt k (_ bv5 8)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "k under bvslt with a bv2nat(k) companion: materialized witness validates (SAT)"
    );
}

// ===========================================================================
// (c) UNSAT stays UNSAT: the promotion only touches the SAT branch; a genuine
//     UNSAT is never weakened to sat/unknown.
// ===========================================================================

/// Range-impossible: `L = bv2nat(k)` with `k:BV8` forces `0 <= L <= 255`, so
/// `L = 300` is UNSAT.
#[test]
#[timeout(60_000)]
fn test_unsat_out_of_range_high() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= L 300))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "bv2nat of an 8-bit k cannot be 300: must stay UNSAT"
    );
}

/// Bridge-only but contradictory Int constraint: `L = bv2nat(k)` (>= 0) with
/// `L < 0` is UNSAT.
#[test]
#[timeout(60_000)]
fn test_unsat_negative_companion() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (< L 0))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "bv2nat(k) >= 0 contradicts L < 0: must stay UNSAT"
    );
}

/// Bridge-only contradiction between two companions: `bv2nat(k) = 5` and
/// `bv2nat(k) = 6` for the SAME `k` is UNSAT.
#[test]
#[timeout(60_000)]
fn test_unsat_conflicting_companions() {
    let smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const A Int)
        (declare-const B Int)
        (assert (= A (bv2nat k)))
        (assert (= B (bv2nat k)))
        (assert (= A 5))
        (assert (= B 6))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "the same bv2nat(k) cannot equal both 5 and 6: must stay UNSAT"
    );
}

// ===========================================================================
// (d) Realizability spot-check: for a promoted model the opaque `bv2nat(k)`
//     value is pinned, and the witness `k = int2bv_w(v)` reproduces it. The
//     negation of the pinned value is therefore UNSAT, confirming the model is
//     not a spurious assignment.
// ===========================================================================

/// `L = bv2nat(k)` with `L = 5` is SAT (promoted); forcing `bv2nat(k) != 5` on
/// top is UNSAT — the companion pins `bv2nat(k)` to exactly 5, witnessed by
/// `k = int2bv_8(5) = #x05` (`bv2nat(#x05) = 5`).
#[test]
#[timeout(60_000)]
fn test_realizability_pinned_value_negation_unsat() {
    let sat_smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= L 5))
        (check-sat)
    "#;
    assert_eq!(verdict(sat_smt), "sat", "promoted SAT model exists");

    let neg_smt = r#"
        (set-logic ALL)
        (declare-const k (_ BitVec 8))
        (declare-const L Int)
        (assert (= L (bv2nat k)))
        (assert (= L 5))
        (assert (not (= (bv2nat k) 5)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(neg_smt),
        "unsat",
        "bv2nat(k) is pinned to 5 (realizable by k = int2bv_8(5)); negating it is UNSAT"
    );
}

/// Realizability of the explicit `int2bv` witness: adding the reconstruction
/// `k = int2bv_8(5)` to the pinned companion stays SAT (the witness is
/// consistent with the model), and `bv2nat(int2bv_8(5)) = 5` holds.
#[test]
#[timeout(60_000)]
fn test_realizability_explicit_int2bv_witness_consistent() {
    // bv2nat(int2bv_8(5)) folds to 5, so this whole conjunction is SAT only if
    // the witness reproduces the pinned value — a direct realizability check.
    let smt = r#"
        (set-logic ALL)
        (declare-const L Int)
        (assert (= L (bv2nat ((_ int2bv 8) 5))))
        (assert (= L 5))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "k = int2bv_8(5) reproduces bv2nat = 5: witness is consistent"
    );
}
