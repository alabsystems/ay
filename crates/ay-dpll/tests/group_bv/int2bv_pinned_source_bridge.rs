// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV<->LIA bridge: int2bv constant-source fold + general (variable-RHS)
//! unsigned-compare bridge (#int2bv-pin).
//!
//! DEDUCTIVE_CHECKS's frame / collection encoder bridges a fixed sequence length to a
//! BV index through `int2bv_w(len)` and guards element access with
//! `bvult idx len_idx`. Two conservative gaps used to leave such queries
//! `unknown (incomplete)`:
//!
//!   1. A bare `int2bv_w(len)` stayed opaque even when `len` was pinned to a
//!      concrete Int (`len == 3`): the residue/injectivity facts relate a
//!      `bv2nat(int2bv(..))` residue or pin a `bv2nat` argument onto an int2bv
//!      WITNESS, but never fold `int2bv` of a fixed source to its bitvector
//!      constant. `collect_int2bv_pinned_source_assertions` now emits the sound
//!      definitional equality `int2bv_w(len) = <bv const (len mod 2^w)>`.
//!
//!   2. `bvult`/`bvule` was only bridged to LIA when one side was a BV constant.
//!      `push_unsigned_bv_cmp_bridge` now also emits the exact
//!      `bvult(a,b) <-> bv2nat(a) < bv2nat(b)` order for two variable operands
//!      (mirroring the signed-compare arm), so a `bvult idx len` guard
//!      discharges once `bv2nat(len)` is pinned by a separate fact.
//!
//! SOUNDNESS: both additions assert theorems of the `int2bv`/`bv2nat` semantics
//! (a fold of a fixed source; an exact unsigned-order equivalence), so they
//! remove no model — SAT stays SAT, UNSAT stays sound. The `false_*` /
//! `*_consistent_*` cases are the gate: a genuinely-SAT query must NEVER be
//! reported `unsat` (a false Verified is a cardinal violation).

use ntest::timeout;

fn verdict(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .into_iter()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "<none>".to_string())
}

// ===========================================================================
// int2bv constant-source fold
// ===========================================================================

/// `len` pinned to 3 by an equality, `y = int2bv(len)`, then `y != 0x…03` is
/// UNSAT: `int2bv(3) = 0x…03`. Base revision left the symbolic `int2bv(len)`
/// opaque and returned `unknown`.
#[test]
#[timeout(60_000)]
fn test_int2bv_pinned_source_eq_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const len Int)
        (declare-const y (_ BitVec 64))
        (assert (= len 3))
        (assert (= y ((_ int2bv 64) len)))
        (assert (not (= y #x0000000000000003)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "int2bv of a source pinned to 3 must fold to 0x…03"
    );
}

/// The same pin via two-sided BOUNDS (`len <= 3 /\ len >= 3`) rather than a
/// direct equality — exercises the `lower == upper` branch of the fold.
#[test]
#[timeout(60_000)]
fn test_int2bv_pinned_source_bounds_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const len Int)
        (declare-const y (_ BitVec 64))
        (assert (<= len 3))
        (assert (>= len 3))
        (assert (= y ((_ int2bv 64) len)))
        (assert (not (= y #x0000000000000003)))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}

/// SOUNDNESS: `len` pinned to 3 and `y = int2bv(len)` with `y = 0x…03` is
/// CONSISTENT — must NOT be reported `unsat`.
#[test]
#[timeout(60_000)]
fn test_int2bv_pinned_source_consistent_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const len Int)
        (declare-const y (_ BitVec 64))
        (assert (= len 3))
        (assert (= y ((_ int2bv 64) len)))
        (assert (= y #x0000000000000003))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "consistent pin (y = int2bv(3) = 0x…03) must never be UNSAT"
    );
}

/// SOUNDNESS: `len` pinned to 5, so `int2bv(len) = 0x…05 != 0x…03`; requiring
/// `y != 0x…03` is CONSISTENT (y = 0x…05). Must NOT be `unsat`.
#[test]
#[timeout(60_000)]
fn test_int2bv_pinned_source_wrong_const_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const len Int)
        (declare-const y (_ BitVec 64))
        (assert (= len 5))
        (assert (= y ((_ int2bv 64) len)))
        (assert (not (= y #x0000000000000003)))
        (check-sat)
    "#;
    assert_ne!(verdict(smt), "unsat");
}

// ===========================================================================
// General (variable-RHS) unsigned-compare bridge
// ===========================================================================

/// The frame-guard core: `bv2nat(len_idx) = 3`, so `int2bv(len)=0x…03` pins
/// `len_idx` (via the injectivity clause), and the guard `bvult idx len_idx`
/// combined with `bvuge idx int2bv(len)` is a contradiction. Requires both the
/// pinned-source fold AND the variable-RHS `bvult` bridge.
#[test]
#[timeout(60_000)]
fn test_frame_guard_var_rhs_bvult_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const len_s_new Int)
        (declare-const len_idx (_ BitVec 64))
        (declare-const idx (_ BitVec 64))
        (assert (= len_s_new 3))
        (assert (= (bv2nat len_idx) len_s_new))
        (assert (bvult idx len_idx))
        (assert (bvuge idx ((_ int2bv 64) len_s_new)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "bvult idx len_idx with bv2nat(len_idx)=3 and idx >= int2bv(3) is UNSAT"
    );
}

/// Variable-RHS `bvult` bridged directly: `bv2nat(b) = 2`, `bvult 0x…05 b`
/// asserts `5 < 2` — UNSAT. Base revision only bridged constant-RHS compares.
#[test]
#[timeout(60_000)]
fn test_var_rhs_bvult_direct_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const b (_ BitVec 64))
        (assert (= (bv2nat b) 2))
        (assert (bvult #x0000000000000005 b))
        (check-sat)
    "#;
    assert_eq!(verdict(smt), "unsat");
}

/// SOUNDNESS: variable-RHS `bvult` that is genuinely SATISFIABLE must not be
/// refuted. `bv2nat(b) = 9`, `bvult 0x…05 b` asserts `5 < 9` — SAT.
#[test]
#[timeout(60_000)]
fn test_var_rhs_bvult_satisfiable_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const b (_ BitVec 64))
        (assert (= (bv2nat b) 9))
        (assert (bvult #x0000000000000005 b))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "5 < 9 is satisfiable — must never be UNSAT"
    );
}

// ===========================================================================
// Indeterminate-polarity (biconditional) unsigned-compare bridge
// ===========================================================================

/// The exact frame-invariant shape: the guard `bvult 0 li` sits inside a
/// disjunction `(or q (not (bvult 0 li)))`, so its polarity is indeterminate and
/// the one-directional bridge cannot fire. With `bv2nat(li) = 3`, the reified
/// biconditional forces `bvult 0 li` true (`0 < 3`), hence `q`; asserting
/// `(not q)` is then UNSAT.
#[test]
#[timeout(60_000)]
fn test_disjunction_guarded_bvult_decided_true() {
    let smt = r#"
        (set-logic ALL)
        (declare-const li (_ BitVec 64))
        (declare-const q Bool)
        (assert (= (bv2nat li) 3))
        (assert (or q (not (bvult #x0000000000000000 li))))
        (assert (not q))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "guard bvult(0, li) with bv2nat(li)=3 is true, forcing q; (not q) is UNSAT"
    );
}

/// The dual: the guard is genuinely FALSE. `bv2nat(li) = 3`, guard
/// `bvult 5 li` = `5 < 3` = false, so `(not (bvult 5 li))` satisfies the
/// disjunction with `q` free — `(not q)` is then CONSISTENT. Must NOT be UNSAT.
#[test]
#[timeout(60_000)]
fn test_disjunction_guarded_bvult_decided_false_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const li (_ BitVec 64))
        (declare-const q Bool)
        (assert (= (bv2nat li) 3))
        (assert (or q (not (bvult #x0000000000000005 li))))
        (assert (not q))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "guard bvult(5, li) with bv2nat(li)=3 is false; (not q) is consistent"
    );
}

// ===========================================================================
// Signed-compare: msb<->bv2nat link + bv2nat constant-pin + signed biconditional
// ===========================================================================

/// msb<->bv2nat link: `bv2nat(x) = 10` fixes the sign (10 < 2^31 so msb = 0),
/// so `bvslt x 0` is false — asserting it is UNSAT. Base revision left `msb`
/// unlinked from `bv2nat`, so both signs were admissible and this was `unknown`.
#[test]
#[timeout(60_000)]
fn test_signed_msb_bv2nat_link_refutes() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x (_ BitVec 32))
        (declare-const li (_ BitVec 64))
        (assert (= (bv2nat li) 3))
        (assert (= (bv2nat x) 10))
        (assert (bvslt x #x00000000))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "bv2nat(x)=10 (< 2^31) forces msb=0, so bvslt x 0 is false"
    );
}

/// SOUNDNESS: a large `bv2nat` DOES set the sign negative — `bv2nat(x)=2^31`
/// means msb=1, so `bvslt x 0` is TRUE and `(not (bvslt x 0))` is UNSAT, but the
/// plain `bvslt x 0` here is SAT and must not be refuted.
#[test]
#[timeout(60_000)]
fn test_signed_msb_link_negative_half_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x (_ BitVec 32))
        (assert (= (bv2nat x) 2147483648))
        (assert (bvslt x #x00000000))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "bv2nat(x)=2^31 => msb=1 => x is negative; bvslt x 0 holds"
    );
}

/// bv2nat constant-pin (conditional): `x` is pinned to `0x0a` by a
/// disjunction-guard collapse (`bv2nat(li)=3` forces `bvult 0 li` true), then
/// `bvslt x 0` with `x = 0x0a` (= 10, non-negative) is UNSAT — exercises the
/// derived-equality congruence pin + the signed biconditional together.
#[test]
#[timeout(60_000)]
fn test_derived_const_pin_signed_refute() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x (_ BitVec 32))
        (declare-const li (_ BitVec 64))
        (assert (= (bv2nat li) 3))
        (assert (or (= x #x0000000a) (not (bvult #x0000000000000000 li))))
        (assert (or (bvslt x #x00000000) (bvslt x #xfffffff0)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "x forced to 0x0a=10; bvslt 10 0 and bvslt 10 0xfffffff0(-16) are both false"
    );
}

/// SOUNDNESS dual: with `bv2nat(li)=0` the guard `bvult 0 li` is FALSE, so `x`
/// is NOT pinned and `bvslt x 0` is satisfiable (x negative). Must NOT be UNSAT.
#[test]
#[timeout(60_000)]
fn test_derived_const_pin_guard_false_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x (_ BitVec 32))
        (declare-const li (_ BitVec 64))
        (assert (= (bv2nat li) 0))
        (assert (or (= x #x0000000a) (not (bvult #x0000000000000000 li))))
        (assert (bvslt x #x00000000))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "guard false => x unpinned => bvslt x 0 is SAT"
    );
}

/// Full quantified frame composition (the VerifyThis shape, minus the
/// last-element access): a BV64-binder frame invariant `forall idx. idx < len ->
/// s_new[idx] = (store s 1 val)[idx]`, `bv2nat(len)=3` (disjunction-guarded),
/// concrete non-negative `s[0..3]` and bounded `val`, and the negated goal
/// `exists i<3. s_new[i] < 0`. Discharges (UNSAT) via E-matching the frame at
/// 0/1/2 + the pinned-index guard + the constant-pin + signed biconditional.
#[test]
#[timeout(90_000)]
fn test_quantified_frame_invariant_signed_nonneg_discharges() {
    let smt = r#"
        (set-logic ALL)
        (declare-const val (_ BitVec 32))
        (declare-const lsn Int)
        (declare-const s_new (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const li (_ BitVec 64))
        (assert (<= 0 lsn))
        (assert (= lsn 3))
        (assert (or (= lsn (bv2nat li)) (not (<= 0 lsn))))
        (assert (= (select s #x0000000000000000) #x0000000a))
        (assert (= (select s #x0000000000000001) #x00000014))
        (assert (= (select s #x0000000000000002) #x0000001e))
        (assert (and (bvsle #x00000000 val) (bvsle val #x000003e8)))
        (assert (forall ((idx (_ BitVec 64)))
            (or (= (select s_new idx) (select (store s #x0000000000000001 val) idx))
                (not (bvult idx li)))))
        (assert (or (bvslt (select s_new #x0000000000000000) #x00000000)
                    (bvslt (select s_new #x0000000000000001) #x00000000)
                    (bvslt (select s_new #x0000000000000002) #x00000000)))
        (check-sat)
    "#;
    assert_eq!(
        verdict(smt),
        "unsat",
        "frame preserves per-element non-negativity across the update; negated goal is UNSAT"
    );
}

/// SOUNDNESS: the SAME frame with a GENUINE violation — the update writes `val`
/// at index 1 with `val` UNBOUNDED (can be negative), so `s_new[1] < 0` is
/// satisfiable. Must NOT be reported UNSAT (a false Verified would be a
/// soundness catastrophe).
#[test]
#[timeout(90_000)]
fn test_quantified_frame_unbounded_value_not_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-const val (_ BitVec 32))
        (declare-const lsn Int)
        (declare-const s_new (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const li (_ BitVec 64))
        (assert (<= 0 lsn))
        (assert (= lsn 3))
        (assert (or (= lsn (bv2nat li)) (not (<= 0 lsn))))
        (assert (= (select s #x0000000000000000) #x0000000a))
        (assert (= (select s #x0000000000000001) #x00000014))
        (assert (= (select s #x0000000000000002) #x0000001e))
        (assert (forall ((idx (_ BitVec 64)))
            (or (= (select s_new idx) (select (store s #x0000000000000001 val) idx))
                (not (bvult idx li)))))
        (assert (or (bvslt (select s_new #x0000000000000000) #x00000000)
                    (bvslt (select s_new #x0000000000000001) #x00000000)
                    (bvslt (select s_new #x0000000000000002) #x00000000)))
        (check-sat)
    "#;
    assert_ne!(
        verdict(smt),
        "unsat",
        "unbounded val at index 1 => s_new[1] can be negative => genuinely SAT"
    );
}
