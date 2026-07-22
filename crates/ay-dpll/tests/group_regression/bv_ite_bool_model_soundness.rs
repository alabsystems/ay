// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #bv-ite-bool-model: invalid BV models on formulas
//! with a free Bool variable used as a BV `ite` condition.
//!
//! Two model-reconstruction defects conspired to emit an INVALID witness
//! (sat verdict was correct, the model falsified the assertions):
//!
//! 1. A Bool variable bit-blasted only *inside* a BV term (an `ite`
//!    condition) gets its SAT literal from the BV solver's `bitblast_bool`
//!    cache, which was never exported into the model. The emitted model
//!    silently defaulted it to `false` even when the SAT solver satisfied
//!    the mux circuit with `true` (fuzzer seeds 5/432/439, qf_bv fragment).
//! 2. Counterexample minimization "verified" candidate values against
//!    cached compound bit-blast values (`bv_model_cache_fallback`) that were
//!    stale w.r.t. the mutated leaf, zeroing constrained variables
//!    (`v8_0 = #x00` where the assertion requires `v8_0 != #x00`).
//!
//! The bad models escaped validation through Bool(false)-arm delegation
//! overrides in observation.rs, which rubber-stamped a CONCRETE evaluator
//! refutation as Verified{DelegatedSolver}. Those overrides are removed:
//! these tests assert both the verdict AND the semantic validity of the
//! emitted model, re-evaluating the original assertions in Rust.

use ntest::timeout;

/// Extract `(define-fun <name> () Bool <b>)` from model output.
fn model_bool(output: &str, name: &str) -> bool {
    let needle = format!("(define-fun {name} () Bool ");
    let start = output
        .find(&needle)
        .unwrap_or_else(|| panic!("no Bool model entry for {name} in: {output}"));
    let rest = &output[start + needle.len()..];
    rest.trim_start().starts_with("true")
}

/// Extract `(define-fun <name> () (_ BitVec 8) #xNN)` from model output.
fn model_bv8(output: &str, name: &str) -> u8 {
    let needle = format!("(define-fun {name} () (_ BitVec 8) #x");
    let start = output
        .find(&needle)
        .unwrap_or_else(|| panic!("no BV8 model entry for {name} in: {output}"));
    let hex = &output[start + needle.len()..start + needle.len() + 2];
    u8::from_str_radix(hex, 16)
        .unwrap_or_else(|e| panic!("bad BV8 hex '{hex}' for {name}: {e}\noutput: {output}"))
}

/// Fuzzer seed 439 (qf_bv): free Bool `b0` conditions a BV `ite`; `v8_0` is
/// constrained by both conjuncts. The pre-fix model was `b0=false,
/// v8_0=#x00`, which falsifies the assertion (`bvnot(#x00)=#xff`,
/// `bvsub(#x41,#x00)=#x41`, `bvule #xff #x41` is false).
#[test]
#[timeout(60_000)]
fn test_bv_ite_bool_cond_model_is_valid_seed439() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun v8_0 () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (assert (let (($x231 (bvule (bvnot (ite b0 (_ bv43 8) v8_0))
                                    (bvsub (bvadd (_ bv253 8) (_ bv68 8)) v8_0))))
            (and (bvslt (_ bv180 8) v8_0) $x231)))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "seed-439 formula is satisfiable (z3 agrees), got: {output}"
    );

    // Re-evaluate the assertion under the emitted model.
    let b0 = model_bool(&output, "b0");
    let v = model_bv8(&output, "v8_0");
    let ite = if b0 { 43u8 } else { v };
    let lhs = !ite; // bvnot
    let rhs = 253u8.wrapping_add(68).wrapping_sub(v); // bvadd/bvsub mod 2^8
    let conj1 = (180u8 as i8) < (v as i8); // bvslt
    let conj2 = lhs <= rhs; // bvule
    assert!(
        conj1 && conj2,
        "emitted model must satisfy the assertion: b0={b0} v8_0={v:#04x} \
         bvslt(180,v)={conj1} bvule({lhs:#04x},{rhs:#04x})={conj2}\noutput: {output}"
    );
}

/// Isolated conjunct (fuzzer seeds 5/432): `v8_0 = #x00` falsifies
/// `(bvult #x00 (bvand v8_0 (ite b0 #x2b v8_0)))` for every `b0`, yet the
/// pre-fix model claimed exactly that.
#[test]
#[timeout(60_000)]
fn test_bv_ite_bool_cond_model_is_valid_isolated_conjunct() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun v8_0 () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (assert (bvult #x00 (bvand v8_0 (ite b0 (_ bv43 8) v8_0))))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "isolated conjunct is satisfiable, got: {output}"
    );

    let b0 = model_bool(&output, "b0");
    let v = model_bv8(&output, "v8_0");
    let ite = if b0 { 43u8 } else { v };
    assert!(
        v & ite > 0,
        "emitted model must satisfy bvult #x00 (bvand v8_0 ite): \
         b0={b0} v8_0={v:#04x} bvand={:#04x}\noutput: {output}",
        v & ite
    );
}

/// `ite` over two constants: with the ite condition dropped from the model,
/// minimization zeroed `v8_0` against the stale cached `bvand` value and the
/// printed `b0=false` selected the wrong mux branch.
#[test]
#[timeout(60_000)]
fn test_bv_ite_const_branches_model_is_valid() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun v8_0 () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (assert (bvult #x00 (bvand v8_0 (ite b0 (_ bv43 8) (_ bv7 8)))))
        (check-sat)
        (get-model)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "const-branch ite formula is satisfiable, got: {output}"
    );

    let b0 = model_bool(&output, "b0");
    let v = model_bv8(&output, "v8_0");
    let ite = if b0 { 43u8 } else { 7u8 };
    assert!(
        v & ite > 0,
        "emitted model must satisfy bvult #x00 (bvand v8_0 ite): \
         b0={b0} v8_0={v:#04x} bvand={:#04x}\noutput: {output}",
        v & ite
    );
}

/// Incremental (push/pop) lane of the seed-439 formula. Pre-fix this lane
/// returned `unknown` (fail-closed on the same broken reconstruction, with
/// no delegation set to mask it). With faithful reconstruction it must
/// return sat WITH a valid model — proof the fail-closed net no longer fires.
#[test]
#[timeout(60_000)]
fn test_bv_ite_bool_cond_incremental_model_is_valid() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun v8_0 () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (push 1)
        (assert (let (($x231 (bvule (bvnot (ite b0 (_ bv43 8) v8_0))
                                    (bvsub (bvadd (_ bv253 8) (_ bv68 8)) v8_0))))
            (and (bvslt (_ bv180 8) v8_0) $x231)))
        (check-sat)
        (get-model)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("sat"),
        "incremental lane must also solve the seed-439 formula, got: {output}"
    );

    let b0 = model_bool(&output, "b0");
    let v = model_bv8(&output, "v8_0");
    let ite = if b0 { 43u8 } else { v };
    let lhs = !ite;
    let rhs = 253u8.wrapping_add(68).wrapping_sub(v);
    let conj1 = (180u8 as i8) < (v as i8);
    let conj2 = lhs <= rhs;
    assert!(
        conj1 && conj2,
        "incremental emitted model must satisfy the assertion: b0={b0} \
         v8_0={v:#04x} bvslt={conj1} bvule({lhs:#04x},{rhs:#04x})={conj2}\noutput: {output}"
    );
}
