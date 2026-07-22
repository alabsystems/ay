// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Sound modular BV<->LIA bridge for `bv2nat(bvadd(a,b))` / `bv2nat(bvsub(a,b))`
//! (#overflow-mod).
//!
//! The conservative bridge relates `bv2nat`/`int2bv`/compares to Int but left a
//! `bvadd`/`bvsub` result opaque, so a no-wrap obligation like
//! `a < 100 && b < 100 ==> add(a,b) == a + b` returned `unknown` — nothing
//! related `bv2nat(bvadd(a,b))` to `bv2nat(a) + bv2nat(b)`.
//!
//! The bridge now emits the definitional modular identity as a two-branch
//! carry/borrow DISJUNCTION plus the result range:
//!
//! ```text
//!   bvadd:  bv2nat(t) = bv2nat(a)+bv2nat(b)  OR  bv2nat(t) = bv2nat(a)+bv2nat(b) - 2^W
//!   bvsub:  bv2nat(t) = bv2nat(a)-bv2nat(b)  OR  bv2nat(t) = bv2nat(a)-bv2nat(b) + 2^W
//!   plus    0 <= bv2nat(t) <= 2^W - 1
//! ```
//!
//! A DISJUNCTION (not a `2^W*carry` product) is used deliberately: ay's LIA path
//! decides the disjunctive form but returns `unknown` on the `const*var` product
//! once >=2 `bv2nat` terms co-occur. SOUNDNESS: the identity is a theorem of the
//! mod-`2^W` semantics — it removes no model, so it can only decide more valid
//! UNSATs and NEVER produces a false UNSAT (a genuine wrap value stays SAT /
//! fail-closed `unknown`, never `unsat`).

use ntest::timeout;

fn verdict(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

/// The documented gain: a no-wrap `bvadd` obligation under the `bv2nat` bridge.
/// `a < 100 && b < 100` implies `bvadd(a,b) == a + b` (no wrap), so the negated
/// goal is UNSAT. On the base revision this returned `unknown (incomplete)`.
#[test]
#[timeout(60_000)]
fn test_no_wrap_bvadd_proof_decided() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (assert (< (bv2nat a) 100))
        (assert (< (bv2nat b) 100))
        (assert (not (= (bv2nat (bvadd a b)) (+ (bv2nat a) (bv2nat b)))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "no-wrap bvadd obligation must now be decided (UNSAT)"
    );
}

/// No-underflow `bvsub` obligation: `b <= a ==> bvsub(a,b) == a - b`.
#[test]
#[timeout(60_000)]
fn test_no_underflow_bvsub_proof_decided() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (assert (<= (bv2nat b) (bv2nat a)))
        (assert (not (= (bv2nat (bvsub a b)) (- (bv2nat a) (bv2nat b)))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "no-underflow bvsub obligation must now be decided (UNSAT)"
    );
}

/// SOUNDNESS: a genuine WRAP value must NOT become a false UNSAT. `bvadd(200,200)`
/// at width 8 is `144` (400 mod 256); a model asserting exactly that is
/// satisfiable, so the bridge must never answer `unsat`. (It stays fail-closed
/// `unknown` — the SAT promotion for a non-bridge-only term is a separate gap —
/// but crucially not `unsat`.)
#[test]
#[timeout(60_000)]
fn test_genuine_bvadd_wrap_value_not_false_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (assert (= (bv2nat a) 200))
        (assert (= (bv2nat (bvadd a a)) 144))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "true wrap value 144 must never be a false UNSAT"
    );
}

/// SOUNDNESS: a genuine `bvsub` underflow value must NOT become a false UNSAT.
/// `bvsub(3,5)` at width 8 is `254` (-2 mod 256).
#[test]
#[timeout(60_000)]
fn test_genuine_bvsub_wrap_value_not_false_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= (bv2nat a) 3))
        (assert (= (bv2nat b) 5))
        (assert (= (bv2nat (bvsub a b)) 254))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "true underflow value 254 must never be a false UNSAT"
    );
}

/// SOUNDNESS: asserting a WRONG modular value must be UNSAT. `bvadd(200,200)`
/// at width 8 is `144`, so `== 100` is genuinely unsatisfiable.
#[test]
#[timeout(60_000)]
fn test_wrong_bvadd_value_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (assert (= (bv2nat a) 200))
        (assert (= (bv2nat (bvadd a a)) 100))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "wrong modular value 100 must be refuted (UNSAT)"
    );
}

/// The modular identity must hold even in the wrap region: `a >= 2^64 - 2`
/// forces `bvadd(a, 2)` to wrap, so `bvadd(a,2) == a + 2` (unbounded) is
/// unsatisfiable together with the truncated equality — the classic overflow
/// spec. Here we assert the SOUND consequence directly: bv2nat(bvadd(a,2)) is at
/// most 1 when bv2nat(a) is 2^64-1, so it cannot equal bv2nat(a)+2.
#[test]
#[timeout(60_000)]
fn test_wrap_region_bvadd_forced_value() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 64))
        (assert (= (bv2nat a) 18446744073709551615))
        (assert (not (= (bv2nat (bvadd a (_ bv2 64))) 1)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "bvadd(2^64-1, 2) wraps to 1; asserting otherwise is UNSAT"
    );
}

/// PIECE 2 — the wrapping overflow REFUTATION (SAT counterexample). The truncated
/// `add(a,2)` differs from the unbounded `a as nat + 2` exactly when `a + 2`
/// overflows, so `bv2nat(bvadd(a,2)) != bv2nat(a) + 2` is SATISFIABLE (witness
/// a = 2^64-1). Piece 1 forces the AUFLIA model into the wrap branch; Piece 2
/// materializes the leaf from its bv2nat companion and validates the concrete
/// witness, promoting it to a genuine SAT. This is upstream Verus's
/// `test_overflow_spec_fails_1`, previously fail-closed `unknown`.
#[test]
#[timeout(60_000)]
fn test_wrapping_overflow_refutation_is_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 64))
        (assert (not (= (bv2nat (bvadd a (_ bv2 64))) (+ (bv2nat a) 2))))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "wrapping add(a,2) != a+2 is refutable (SAT witness a = 2^64-1)"
    );
}

/// SOUNDNESS (Piece 2, cardinal): the materialized-model promotion must NEVER
/// produce a false SAT for a query whose BV constraints the AUFLIA layer treated
/// opaquely. Here `bv2nat(a)=3, bv2nat(b)=5` with `not(bvult a b)`: concretely
/// `3 <u 5` holds, so `not(bvult a b)` is false and the query is UNSAT. The
/// concrete-recompute in `validate_model` must reject the spurious AUFLIA model.
#[test]
#[timeout(60_000)]
fn test_materialize_rejects_opaque_bv_inconsistency() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= (bv2nat a) 3))
        (assert (= (bv2nat b) 5))
        (assert (not (bvult a b)))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "sat",
        "a=3,b=5 with not(bvult a b) is UNSAT — must never be a false SAT"
    );
}

/// SOUNDNESS (Piece 2): a wrap-region bvult inconsistency must be rejected.
/// `bv2nat(a)=100` with `bvult(bvadd(a,a), a)` asserts `200 <u 100` (false at
/// width 8, since bvadd(100,100)=200 does not wrap), so the query is UNSAT.
#[test]
#[timeout(60_000)]
fn test_materialize_rejects_false_wrap_bvult() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (assert (= (bv2nat a) 100))
        (assert (bvult (bvadd a a) a))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "sat",
        "bvadd(100,100)=200 does not wrap so 200 <u 100 is false — UNSAT, never false SAT"
    );
}

/// Piece 2 positive: a CONSISTENT wrap-region SAT. `bv2nat(a)=200` with
/// `bvult(bvadd(a,a), a)` asserts `144 <u 200` (bvadd(200,200)=144 wraps), which
/// is true — a genuine SAT the materialized witness validates.
#[test]
#[timeout(60_000)]
fn test_materialize_accepts_consistent_wrap_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const a (_ BitVec 8))
        (assert (= (bv2nat a) 200))
        (assert (bvult (bvadd a a) a))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "sat",
        "bvadd(200,200)=144 wraps so 144 <u 200 is true — genuine SAT"
    );
}
