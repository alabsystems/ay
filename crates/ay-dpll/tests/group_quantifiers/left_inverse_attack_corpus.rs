// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Attack corpus around the left-inverse SAT-certificate shape and its
//! guarded-forall / finite-pigeonhole neighbors (#2774 false-controls,
//! #boolarg-congruence class).
//!
//! Every expected verdict below was adjudicated three ways before landing:
//! manual semantics, z3 (all exact), and the current solver (all exact) —
//! per the #8969 oracle-skepticism discipline. The UNSAT cases are the
//! attacks: each one gives the certificate (or the ground layer) a chance to
//! certify a wrong `sat`. The SAT cases are controls pinning that the
//! refutation machinery does not overreach into wrong `unsat`.
//!
//! Assertions are exact on purpose: a flip to the opposite verdict is a
//! soundness hole, and a downgrade to `unknown` is a completeness regression
//! we also want to catch at this corpus.

use ntest::timeout;

fn expect_verdict(smt: &str, expected: &str, label: &str) {
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec![expected.to_string()], "{label}");
}

// ---------------------------------------------------------------------------
// A-series: the left-inverse axiom itself (Unbox . Box = id).
// ---------------------------------------------------------------------------

/// Left inverse forces Box injective; a merged Box image with distinct
/// preimages is the direct blocking attack.
#[test]
#[timeout(60_000)]
fn a1_blocking_merged_box_image_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b))
        (assert (= (Box a) (Box b)))
        (check-sat)
        "#,
        "unsat",
        "a1: distinct a b with Box a = Box b contradicts left inverse",
    );
}

/// Control: the same axiom with the Box images kept distinct is satisfiable.
#[test]
#[timeout(60_000)]
fn a10_sat_control_distinct_images_sat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b))
        (assert (distinct (Box a) (Box b)))
        (check-sat)
        "#,
        "sat",
        "a10: injective Box with distinct images is the SAT control",
    );
}

/// The bare pigeonhole with no ground anchor at all: BV8 -> Bool left
/// inverse asserts a 256-into-2 injection. This is the #boolarg-congruence
/// wrong-SAT shape minus the `(= (BoolBox w) true)` anchor.
#[test]
#[timeout(60_000)]
fn a11_pigeonhole_bool_unanchored_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun Box ((_ BitVec 8)) Bool)
        (declare-fun Unbox (Bool) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (check-sat)
        "#,
        "unsat",
        "a11: 256 -> 2 left inverse is a pigeonhole UNSAT even unanchored",
    );
}

/// The a1 attack laundered through fresh V-sorted constants so the merged
/// image is only discoverable through equality chaining.
#[test]
#[timeout(60_000)]
fn a2_chained_through_aliases_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c V)
        (declare-const d V)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b))
        (assert (= c (Box a)))
        (assert (= d (Box b)))
        (assert (= c d))
        (check-sat)
        "#,
        "unsat",
        "a2: alias chain c = Box a = Box b = d still merges the images",
    );
}

/// Three-way distinct with one merged pair: the contradiction only needs the
/// merged pair, the third element is decoy universe enlargement.
#[test]
#[timeout(60_000)]
fn a3_distinct3_with_decoy_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const cc U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b cc))
        (assert (= (Box a) (Box b)))
        (check-sat)
        "#,
        "unsat",
        "a3: the decoy third element must not let the merged pair slip through",
    );
}

/// Two stacked left-inverse pairs: the composition B2 . B1 is injective, so
/// merging the outer images with distinct innermost preimages is UNSAT. A
/// certificate that treats each axiom in isolation must not certify this.
#[test]
#[timeout(60_000)]
fn a4_nested_composition_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-sort W 0)
        (declare-fun B1 (U) V)
        (declare-fun U1 (V) U)
        (declare-fun B2 (V) W)
        (declare-fun U2 (W) V)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (U1 (B1 x)) x) :pattern ((B1 x)))))
        (assert (forall ((y V)) (! (= (U2 (B2 y)) y) :pattern ((B2 y)))))
        (assert (distinct a b))
        (assert (= (B2 (B1 a)) (B2 (B1 b))))
        (check-sat)
        "#,
        "unsat",
        "a4: composed left inverses are jointly injective",
    );
}

/// Interpreted-domain variant: Box over Int with two distinct numerals
/// merged. No uninterpreted-universe enlargement argument applies to Int.
#[test]
#[timeout(60_000)]
fn a5_int_embed_unsat() {
    expect_verdict(
        r#"
        (set-logic UFLIA)
        (declare-sort V 0)
        (declare-fun Box (Int) V)
        (declare-fun Unbox (V) Int)
        (assert (forall ((x Int)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (= (Box 1) (Box 2)))
        (check-sat)
        "#,
        "unsat",
        "a5: Box 1 = Box 2 forces 1 = 2 under the left inverse",
    );
}

/// Same semantics as a1 but the pattern anchors on `(Unbox (Box x))` instead
/// of `(Box x)`. Patterns are instantiation hints, not semantics — the
/// verdict must not change.
#[test]
#[timeout(60_000)]
fn a6_trigger_mismatch_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Unbox (Box x))))))
        (assert (distinct a b))
        (assert (= (Box a) (Box b)))
        (check-sat)
        "#,
        "unsat",
        "a6: a different trigger must not flip the a1 verdict",
    );
}

/// The mirrored axiom: `Box . Unbox = id` makes Unbox injective; merging
/// Unbox results of distinct V constants is the mirrored attack.
#[test]
#[timeout(60_000)]
fn a7_right_inverse_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const b1 V)
        (declare-const b2 V)
        (assert (forall ((y V)) (! (= (Box (Unbox y)) y) :pattern ((Unbox y)))))
        (assert (distinct b1 b2))
        (assert (= (Unbox b1) (Unbox b2)))
        (check-sat)
        "#,
        "unsat",
        "a7: right inverse makes Unbox injective",
    );
}

/// Degenerate self-inverse: `id x = x` with `id a = b`, `distinct a b`. The
/// one-function shape must not be mistaken for a certifiable Box/Unbox pair.
#[test]
#[timeout(60_000)]
fn a8_identity_function_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun id (U) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (id x) x) :pattern ((id x)))))
        (assert (distinct a b))
        (assert (= (id a) b))
        (check-sat)
        "#,
        "unsat",
        "a8: id a = b contradicts id a = a with distinct a b",
    );
}

/// Finite interpreted codomain, BV flavor: BV8 -> BV1 left inverse is a
/// 256-into-2 pigeonhole exactly like the Bool case, but stays entirely
/// inside the bitblaster.
#[test]
#[timeout(60_000)]
fn a9_pigeonhole_bv1_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun Box ((_ BitVec 8)) (_ BitVec 1))
        (declare-fun Unbox ((_ BitVec 1)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (check-sat)
        "#,
        "unsat",
        "a9: 256 -> 2 pigeonhole through BV1 codomain",
    );
}

// ---------------------------------------------------------------------------
// B-series: guarded finite-domain foralls — the guard boundary must bind
// exactly (off-by-one at the boundary would certify wrong SAT).
// ---------------------------------------------------------------------------

/// `x < 5 => f x = 0` with `f 4 = 1`: 4 is INSIDE the strict bound.
#[test]
#[timeout(60_000)]
fn b1_bvult_boundary_inside_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvult x #x05)) (= (f x) #x00))))
        (assert (= (f #x04) #x01))
        (check-sat)
        "#,
        "unsat",
        "b1: index 4 is inside bvult _ 5",
    );
}

/// Control: `f 5 = 1` is OUTSIDE the strict bound — must stay SAT (an
/// over-wide guard expansion would wrongly refute this).
#[test]
#[timeout(60_000)]
fn b2_bvult_outside_sat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvult x #x05)) (= (f x) #x00))))
        (assert (= (f #x05) #x01))
        (check-sat)
        "#,
        "sat",
        "b2: index 5 is outside bvult _ 5 — refuting it would be wrong UNSAT",
    );
}

/// `bvule x #xFF` covers the whole BV8 domain — a vacuity-detector that
/// misreads a full-range guard as empty would certify wrong SAT.
#[test]
#[timeout(60_000)]
fn b3_bvule_full_range_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvule x #xFF)) (= (f x) #x00))))
        (assert (= (f #xFF) #x01))
        (check-sat)
        "#,
        "unsat",
        "b3: bvule _ FF is total on BV8",
    );
}

/// Signed guard: `bvsle x 0` includes #xFF (= -1 signed). Treating the
/// comparison as unsigned would exclude it and certify wrong SAT.
#[test]
#[timeout(60_000)]
fn b4_signed_guard_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvsle x #x00)) (= (f x) #x00))))
        (assert (= (f #xFF) #x01))
        (check-sat)
        "#,
        "unsat",
        "b4: #xFF is -1 under bvsle and inside the guard",
    );
}

/// High-end range guard: `x >= 254` — expansion from the top of the domain
/// must not overflow-wrap or skip the extremes.
#[test]
#[timeout(60_000)]
fn b5_high_range_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvuge x #xFE)) (= (f x) #x00))))
        (assert (= (f #xFF) #x01))
        (check-sat)
        "#,
        "unsat",
        "b5: #xFF is inside bvuge _ FE",
    );
}

/// Width-1 guarded: the smallest domain where boundary arithmetic can wrap.
#[test]
#[timeout(60_000)]
fn b6_width1_guarded_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (or (not (bvule x #b1)) (= (f x) #b0))))
        (assert (= (f #b1) #b1))
        (check-sat)
        "#,
        "unsat",
        "b6: total guard on BV1",
    );
}

/// Width-1 unguarded: bare total forall over BV1.
#[test]
#[timeout(60_000)]
fn b7_width1_unguarded_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
        (assert (forall ((x (_ BitVec 1))) (= (f x) #b0)))
        (assert (= (f #b1) #b1))
        (check-sat)
        "#,
        "unsat",
        "b7: unguarded BV1 forall",
    );
}

/// Int-domain double guard `0 <= x <= 4` with the violation at the upper
/// boundary point.
#[test]
#[timeout(60_000)]
fn b8_int_guard_boundary_unsat() {
    expect_verdict(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (or (< x 0) (> x 4) (= (f x) 0))))
        (assert (= (f 4) 1))
        (check-sat)
        "#,
        "unsat",
        "b8: x = 4 satisfies 0 <= x <= 4",
    );
}

/// Control: an extra escape disjunct `(< x c)` with `c = 10` makes the
/// x = 4 instance vacuously true — the guard set must be read as a whole,
/// not clause-by-clause. Refuting this would be wrong UNSAT.
#[test]
#[timeout(60_000)]
fn b9_guard_must_bind_sat() {
    expect_verdict(
        r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const c Int)
        (assert (forall ((x Int)) (or (< x 0) (> x 4) (< x c) (= (f x) 0))))
        (assert (= (f 4) 1))
        (assert (= c 10))
        (check-sat)
        "#,
        "sat",
        "b9: the (< x c) escape disjunct discharges the x = 4 instance",
    );
}

// ---------------------------------------------------------------------------
// C-series: congruence-through-guard and scale attacks.
// ---------------------------------------------------------------------------

/// Guarded left inverse `x < 8 => g (f x) = x` with a merged f-image inside
/// the guard: needs congruence THROUGH the guarded instances.
#[test]
#[timeout(60_000)]
fn c1_guard_congruence_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (declare-fun g ((_ BitVec 4)) (_ BitVec 4))
        (assert (forall ((x (_ BitVec 4))) (or (not (bvult x #x8)) (= (g (f x)) x))))
        (assert (= (f #x2) (f #x3)))
        (check-sat)
        "#,
        "unsat",
        "c1: f 2 = f 3 forces g(f 2) = 2 = 3 inside the guard",
    );
}

/// Width-64 top-of-domain guard: no finite expansion of 2^64 exists, so the
/// refutation must come from the symbolic route without wrong SAT from a
/// bailed-out expansion.
#[test]
#[timeout(60_000)]
fn c2_width64_boundary_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 64)) (_ BitVec 64))
        (assert (forall ((x (_ BitVec 64))) (or (not (bvuge x #xFFFFFFFFFFFFFFFE)) (= (f x) #x0000000000000000))))
        (assert (= (f #xFFFFFFFFFFFFFFFF) #x0000000000000001))
        (check-sat)
        "#,
        "unsat",
        "c2: two-element guard at the top of BV64",
    );
}

/// Deep nesting: `Box (Unbox (Box a)) = Box b` reduces to `Box a = Box b`
/// via the axiom instance at `a`, then to `a = b` via congruence + the
/// instance at `b`.
#[test]
#[timeout(60_000)]
fn c3_deep_nest_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b))
        (assert (= (Box (Unbox (Box a))) (Box b)))
        (check-sat)
        "#,
        "unsat",
        "c3: rewrite through the nested occurrence still reaches a = b",
    );
}

/// The exact a1 attack with NO set-logic line: logic inference must not
/// route it to a laxer path that certifies wrong SAT.
#[test]
#[timeout(60_000)]
fn c4_no_set_logic_unsat() {
    expect_verdict(
        r#"
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const b U)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct a b))
        (assert (= (Box a) (Box b)))
        (check-sat)
        "#,
        "unsat",
        "c4: verdict must not depend on the set-logic header",
    );
}

// ---------------------------------------------------------------------------
// D-series: injectivity direction and vacuity controls.
// ---------------------------------------------------------------------------

/// Explicit Unbox-injectivity forall (no Box roundtrip): distinct c d with
/// merged Unbox results.
#[test]
#[timeout(60_000)]
fn d1_unbox_injective_forall_unsat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const c V)
        (declare-const d V)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (forall ((y V) (z V)) (=> (= (Unbox y) (Unbox z)) (= y z))))
        (assert (distinct c d))
        (assert (= (Unbox c) (Unbox d)))
        (check-sat)
        "#,
        "unsat",
        "d1: asserted injectivity refutes the merged Unbox pair",
    );
}

/// Exists under a guard with the witness domain exhausted: x in {0,1} and
/// both mapped away from 7 — the exists has no witness.
#[test]
#[timeout(60_000)]
fn d2_exists_guard_exhausted_unsat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 4)) (_ BitVec 4))
        (assert (exists ((x (_ BitVec 4))) (and (bvult x #x2) (= (f x) #x7))))
        (assert (= (f #x0) #x0))
        (assert (= (f #x1) #x1))
        (check-sat)
        "#,
        "unsat",
        "d2: both guard-admissible witnesses are pinned away from 7",
    );
}

/// Control: `bvult x #x00` is unsatisfiable, so the guarded forall is
/// vacuously true and the ground anchor is free.
#[test]
#[timeout(60_000)]
fn d3_empty_range_vacuous_sat() {
    expect_verdict(
        r#"
        (set-logic UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((x (_ BitVec 8))) (or (not (bvult x #x00)) (= (f x) #xAA))))
        (assert (= (f #x03) #x01))
        (check-sat)
        "#,
        "sat",
        "d3: empty guard range makes the forall vacuous — wrong UNSAT here would be unsound",
    );
}

/// Control: without an injectivity axiom for Unbox, two distinct V constants
/// may share an Unbox value that happens to hit the Box preimage `a` — the
/// left inverse alone does NOT make Unbox injective off the Box image.
#[test]
#[timeout(60_000)]
fn d4_offimage_merge_sat() {
    expect_verdict(
        r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-fun Box (U) V)
        (declare-fun Unbox (V) U)
        (declare-const a U)
        (declare-const c V)
        (declare-const d V)
        (assert (forall ((x U)) (! (= (Unbox (Box x)) x) :pattern ((Box x)))))
        (assert (distinct c d))
        (assert (= (Unbox c) a))
        (assert (= (Unbox d) a))
        (check-sat)
        "#,
        "sat",
        "d4: Unbox is not injective off the Box image — refuting this would overreach",
    );
}
