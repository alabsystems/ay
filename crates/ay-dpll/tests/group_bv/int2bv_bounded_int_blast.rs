// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! BV<->LIA bridge: masking/shifting obligations over Int-lifted integers
//! (#int2bv-invalid-model).
//!
//! Measured 2026-09-10 while verifying `library/core` with compiler_consumer: 1,161
//! `[AY SOUNDNESS GATE] caught an INVALID model` banners in ~40 minutes, all on
//! mixed Int/BitVec assertions of the shapes below — `bv2nat` of a `bvshl`,
//! `bvand`, `bvlshr`, `extract`/`sign_extend` over `int2bv` of an Int local.
//! Two defects, one visible:
//!
//!   1. The AUFLIA lane behind the bridge treats every BitVec operator as an
//!      uninterpreted function, so its SAT candidate (`v0 = 1, v3 = 1` for
//!      `v3 = bv2nat(bvshl #x1 (int2bv 64 v0))`) is spurious. The bridge's
//!      promotion validator then DELEGATED the definition even though the
//!      evaluator had concretely refuted it — `contains_uninterpreted_function_app`
//!      classified `bv2nat`/`bvshl`/`int2bv` as UF — and published `sat` with a
//!      falsified model; the independent gate downgraded it to `unknown`.
//!      FIXED at the root (interpreted BV/conversion operators are never a "UF
//!      model-extraction gap") and belt-and-braces (the bridge promotes only on
//!      independent evidence).
//!   2. With the false promotion gone the query would merely stall at
//!      `unknown`. `int_blast.rs` now DECIDES it: Int variables with proven
//!      bounds become signed W-bit vectors, residue-only ones (occurring solely
//!      under `int2bv`) become free vectors, and the eager bit-blaster gives the
//!      exact verdict; a SAT model is mapped back and re-validated.
//!
//! Every `sat` below checks the PUBLISHED model against the semantics by hand
//! (a `sat` with a false witness is what the banner was about); every `unsat`
//! is a real theorem of the modular semantics (a false UNSAT is a cardinal
//! violation).

use ntest::timeout;

fn run(smt: &str) -> (String, Vec<String>) {
    let lines: Vec<String> = crate::common::solve_vec(smt)
        .into_iter()
        .flat_map(|chunk| chunk.lines().map(str::to_string).collect::<Vec<_>>())
        .collect();
    let verdict = lines
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "<none>".to_string());
    (verdict.trim().to_string(), lines)
}

fn verdict(smt: &str) -> String {
    run(smt).0
}

/// Raw value text of `name` in a `(get-model)` dump.
fn model_value(lines: &[String], name: &str) -> String {
    let needle = format!("(define-fun {name} () ");
    let line = lines
        .iter()
        .find(|line| line.contains(&needle))
        .unwrap_or_else(|| panic!("no model value for {name} in {lines:#?}"));
    let start = line.find(&needle).expect("needle") + needle.len();
    let rest = line[start..].trim_end();
    let rest = rest.strip_suffix(')').unwrap_or(rest);
    let value = if let Some(int) = rest.strip_prefix("Int ") {
        int
    } else if let Some(end) = rest.find(") ") {
        // `(_ BitVec N) value`
        &rest[end + 2..]
    } else {
        panic!("unparsed model line for {name}: {line}")
    };
    value.trim().to_string()
}

fn model_int(lines: &[String], name: &str) -> i128 {
    let value = model_value(lines, name);
    if let Some(inner) = value.strip_prefix("(- ") {
        let inner = inner.trim_end_matches(')').trim();
        -inner
            .parse::<i128>()
            .unwrap_or_else(|_| panic!("int value for {name}: {value}"))
    } else {
        value
            .parse::<i128>()
            .unwrap_or_else(|_| panic!("int value for {name}: {value}"))
    }
}

fn model_bv(lines: &[String], name: &str) -> u128 {
    let value = model_value(lines, name);
    if let Some(hex) = value.strip_prefix("#x") {
        u128::from_str_radix(hex, 16).unwrap_or_else(|_| panic!("bv value for {name}: {value}"))
    } else if let Some(bin) = value.strip_prefix("#b") {
        u128::from_str_radix(bin, 2).unwrap_or_else(|_| panic!("bv value for {name}: {value}"))
    } else if let Some(rest) = value.strip_prefix("(_ bv") {
        rest.split_whitespace()
            .next()
            .and_then(|n| n.parse::<u128>().ok())
            .unwrap_or_else(|| panic!("bv value for {name}: {value}"))
    } else {
        panic!("unparsed bv value for {name}: {value}")
    }
}

/// `x mod 2^w` as a non-negative machine integer.
fn residue(x: i128, w: u32) -> u128 {
    let m = 1u128 << w;
    (((x % m as i128) + m as i128) % m as i128) as u128
}

// ===========================================================================
// Shape 1: `v3 = bv2nat(bvshl #x1 (int2bv 64 v0))` — the banner assertion.
// ===========================================================================

const SHL: &str = r#"
    (set-logic ALL)
    (declare-const v0 Int) (declare-const v3 Int)
    (assert (= v3 (bv2nat (bvshl #x0000000000000001 ((_ int2bv 64) v0)))))
"#;

/// `1 << 1 = 2 != 1`: the task's minimal repro must be `unsat`.
#[test]
#[timeout(60_000)]
fn shl_pinned_source_wrong_result_unsat() {
    let smt = format!("{SHL} (assert (= v0 1)) (assert (= v3 1)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// The banner case: only the result pinned. SAT with `v0 ≡ 0 (mod 2^64)`, and
/// the published model must satisfy the definition (the old binary published
/// `v0 = 1, v3 = 1` and the gate downgraded it to `unknown`).
#[test]
#[timeout(60_000)]
fn shl_backward_pin_sat_with_valid_model() {
    let smt = format!("{SHL} (assert (= v3 1)) (check-sat) (get-model)");
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let v0 = model_int(&lines, "v0");
    let v3 = model_int(&lines, "v3");
    let shift = residue(v0, 64);
    let expected: u128 = if shift >= 64 {
        0
    } else {
        (1u128 << shift) & 0xFFFF_FFFF_FFFF_FFFF
    };
    assert_eq!(v3 as u128, expected, "model v0={v0} v3={v3}");
    assert_eq!(v3, 1);
}

/// Bounded shift amount: `1 << v0 = 1024` forces `v0 = 10`.
#[test]
#[timeout(60_000)]
fn shl_bounded_amount_unique_witness_sat() {
    let smt = format!(
        "{SHL} (assert (<= 0 v0)) (assert (< v0 64)) (assert (= v3 1024)) (check-sat) (get-model)"
    );
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "v0"), 10);
    assert_eq!(model_int(&lines, "v3"), 1024);
}

/// `3` is not a power of two: no bounded shift reaches it.
#[test]
#[timeout(60_000)]
fn shl_bounded_amount_non_power_of_two_unsat() {
    let smt = format!("{SHL} (assert (<= 0 v0)) (assert (< v0 64)) (assert (= v3 3)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// SMT-LIB `bvshl` by an amount `>= width` is zero, for every such amount.
#[test]
#[timeout(60_000)]
fn shl_amount_at_or_over_width_is_zero_unsat() {
    let smt = format!(
        "{SHL} (assert (<= 64 v0)) (assert (< v0 18446744073709551616)) \
         (assert (not (= v3 0))) (check-sat)"
    );
    assert_eq!(verdict(&smt), "unsat");
}

// ===========================================================================
// Shape 2: `abs = bv2nat(bvand (int2bv 32 bits) (int2bv 32 m))`.
// ===========================================================================

const AND32: &str = r#"
    (set-logic ALL)
    (declare-const bits Int) (declare-const m Int) (declare-const abs Int)
    (assert (<= 0 bits)) (assert (< bits 4294967296))
    (assert (<= 0 m)) (assert (< m 4294967296))
    (assert (= abs (bv2nat (bvand ((_ int2bv 32) bits) ((_ int2bv 32) m)))))
"#;

/// `bits & m <= bits` for every non-negative 32-bit `bits`.
#[test]
#[timeout(60_000)]
fn and32_result_never_exceeds_operand_unsat() {
    let smt = format!("{AND32} (assert (> abs bits)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// `bits & 0xFF = 0x0F` has witnesses; the published one must satisfy it.
#[test]
#[timeout(60_000)]
fn and32_mask_sat_with_valid_model() {
    let smt = format!("{AND32} (assert (= m 255)) (assert (= abs 15)) (check-sat) (get-model)");
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let bits = model_int(&lines, "bits");
    assert_eq!(residue(bits, 32) & 255, 15, "bits={bits}");
    assert_eq!(model_int(&lines, "abs"), 15);
}

/// `1 & 2 = 0 != 3`.
#[test]
#[timeout(60_000)]
fn and32_pinned_operands_wrong_result_unsat() {
    let smt =
        format!("{AND32} (assert (= bits 1)) (assert (= m 2)) (assert (= abs 3)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// Arithmetic on the bridged value: `3 & 3 = 3 != 3 + 3`, but `= bits` holds.
#[test]
#[timeout(60_000)]
fn and32_result_in_arithmetic_context() {
    let unsat = format!(
        "{AND32} (assert (= abs (+ bits m))) (assert (= bits 3)) (assert (= m 3)) (check-sat)"
    );
    assert_eq!(verdict(&unsat), "unsat");
    let sat =
        format!("{AND32} (assert (= abs bits)) (assert (= bits 3)) (assert (= m 3)) (check-sat)");
    assert_eq!(verdict(&sat), "sat");
}

// ===========================================================================
// Shape 3: `x = bv2nat(bvand (int2bv 64 y) #x…03)` — residue-only source.
// ===========================================================================

const AND64_MASK3: &str = r#"
    (set-logic ALL)
    (declare-const x Int) (declare-const y Int)
    (assert (= x (bv2nat (bvand ((_ int2bv 64) y) #x0000000000000003))))
"#;

/// A 2-bit mask never yields 4, for ANY integer `y` (unbounded: residue-only).
#[test]
#[timeout(60_000)]
fn and64_mask_out_of_range_unsat() {
    let smt = format!("{AND64_MASK3} (assert (= x 4)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// `5 & 3 = 1` (sat), `6 & 3 = 2 != 1` (unsat).
#[test]
#[timeout(60_000)]
fn and64_mask_pinned_source() {
    let sat = format!("{AND64_MASK3} (assert (= y 5)) (assert (= x 1)) (check-sat) (get-model)");
    let (v, lines) = run(&sat);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "y"), 5);
    assert_eq!(model_int(&lines, "x"), 1);
    let unsat = format!("{AND64_MASK3} (assert (= y 6)) (assert (= x 1)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
}

/// Backward pin with a bounded source: `y & 3 = 3` with `0 <= y < 100`.
#[test]
#[timeout(60_000)]
fn and64_mask_backward_pin_bounded_sat() {
    let smt = format!(
        "{AND64_MASK3} (assert (<= 0 y)) (assert (< y 100)) (assert (= x 3)) (check-sat) (get-model)"
    );
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let y = model_int(&lines, "y");
    assert!((0..100).contains(&y), "y={y}");
    assert_eq!(residue(y, 64) & 3, 3, "y={y}");
}

/// A NEGATIVE source: `int2bv` is modular, `-1 mod 2^64` is all ones.
#[test]
#[timeout(60_000)]
fn and64_mask_negative_source() {
    let sat =
        format!("{AND64_MASK3} (assert (= y (- 1))) (assert (= x 3)) (check-sat) (get-model)");
    let (v, lines) = run(&sat);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "y"), -1);
    let unsat = format!("{AND64_MASK3} (assert (= y (- 1))) (assert (= x 1)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
}

// ===========================================================================
// Shape 4: `x = bv2nat(sign_extend 16 (extract 31 16 (int2bv 32 v)))`.
// ===========================================================================

const SEXT: &str = r#"
    (set-logic ALL)
    (declare-const x Int) (declare-const v Int)
    (assert (= x (bv2nat ((_ sign_extend 16) ((_ extract 31 16) ((_ int2bv 32) v))))))
"#;

/// `0x8000_0000 >> 16 = 0x8000`, sign-extended to `0xFFFF_8000 = 4294934528`.
#[test]
#[timeout(60_000)]
fn sext_high_half_negative_sat_and_wrong_unsat() {
    let sat = format!("{SEXT} (assert (= v 2147483648)) (assert (= x 4294934528)) (check-sat)");
    assert_eq!(verdict(&sat), "sat");
    let unsat = format!("{SEXT} (assert (= v 2147483648)) (assert (= x 32768)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
}

/// A non-negative i32 has a clear sign bit: no sign extension can occur.
#[test]
#[timeout(60_000)]
fn sext_nonnegative_source_never_extends_unsat() {
    let smt = format!(
        "{SEXT} (assert (<= 0 v)) (assert (< v 2147483648)) (assert (>= x 2147483648)) (check-sat)"
    );
    assert_eq!(verdict(&smt), "unsat");
}

/// Backward pin `x = 0xFFFF_FFFF` forces the high half of `v` to all ones;
/// `x = 0xFFFF_0000` is unreachable (a set sign bit keeps its own low half).
#[test]
#[timeout(60_000)]
fn sext_backward_pin_sat_with_valid_model() {
    let smt = format!(
        "{SEXT} (assert (<= 0 v)) (assert (< v 4294967296)) (assert (= x 4294967295)) \
         (check-sat) (get-model)"
    );
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let v = model_int(&lines, "v");
    let hi = (residue(v, 32) >> 16) as u32;
    let expected = if hi >= 0x8000 {
        hi as u128 | 0xFFFF_0000
    } else {
        hi as u128
    };
    assert_eq!(model_int(&lines, "x") as u128, expected, "v={v}");
    assert_eq!(hi, 0xFFFF, "v={v}");
    let unreachable = format!(
        "{SEXT} (assert (<= 0 v)) (assert (< v 4294967296)) (assert (= x 4294901760)) (check-sat)"
    );
    assert_eq!(verdict(&unreachable), "unsat");
}

// ===========================================================================
// Shape 5: `(not (= 0 (bv2nat (bvand self (int2bv 32 m)))))` — a free BitVec
// leaf beside an Int source.
// ===========================================================================

const AND_SELF: &str = r#"
    (set-logic ALL)
    (declare-const self (_ BitVec 32)) (declare-const m Int)
    (assert (<= 0 m)) (assert (< m 4294967296))
    (assert (not (= 0 (bv2nat (bvand self ((_ int2bv 32) m))))))
"#;

/// `self & 0 = 0` for every `self`.
#[test]
#[timeout(60_000)]
fn and_self_zero_mask_unsat() {
    let smt = format!("{AND_SELF} (assert (= m 0)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// `7 & 8 = 0`.
#[test]
#[timeout(60_000)]
fn and_self_disjoint_bits_unsat() {
    let smt = format!("{AND_SELF} (assert (= m 8)) (assert (= self #x00000007)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// Free `self`: the witness must actually have bit 3 set.
#[test]
#[timeout(60_000)]
fn and_self_free_leaf_sat_with_valid_model() {
    let smt = format!("{AND_SELF} (assert (= m 8)) (check-sat) (get-model)");
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let this = model_bv(&lines, "self");
    assert_ne!(this & 8, 0, "self={this:#x}");
}

/// Pinned leaf, bounded Int mask: `1 & m != 0` with `m < 2` forces `m = 1`.
#[test]
#[timeout(60_000)]
fn and_self_pinned_leaf_forces_mask_sat() {
    let smt =
        format!("{AND_SELF} (assert (= self #x00000001)) (assert (< m 2)) (check-sat) (get-model)");
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "m"), 1);
}

// ===========================================================================
// Shape 6: `x = bv2nat(bvand (int2bv 8 y) #xc0)`.
// ===========================================================================

const AND8_MASK: &str = r#"
    (set-logic ALL)
    (declare-const x Int) (declare-const y Int)
    (assert (= x (bv2nat (bvand ((_ int2bv 8) y) #xc0))))
"#;

/// `0x10` has a bit outside the mask.
#[test]
#[timeout(60_000)]
fn and8_mask_bit_outside_mask_unsat() {
    let smt = format!("{AND8_MASK} (assert (= x 16)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

/// `200 = 0xC8`, `200 & 0xC0 = 0xC0` (sat); `100 = 0x64`, `& 0xC0 = 0x40` (unsat).
#[test]
#[timeout(60_000)]
fn and8_mask_pinned_source() {
    let sat = format!("{AND8_MASK} (assert (= y 200)) (assert (= x 192)) (check-sat)");
    assert_eq!(verdict(&sat), "sat");
    let unsat = format!("{AND8_MASK} (assert (= y 100)) (assert (= x 192)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
}

/// Backward pin: `y & 0xC0 = 0xC0` with `0 <= y < 256` ⇒ `y >= 192`.
#[test]
#[timeout(60_000)]
fn and8_mask_backward_pin_sat_with_valid_model() {
    let smt = format!(
        "{AND8_MASK} (assert (<= 0 y)) (assert (< y 256)) (assert (= x 192)) (check-sat) (get-model)"
    );
    let (v, lines) = run(&smt);
    assert_eq!(v, "sat", "{lines:#?}");
    let y = model_int(&lines, "y");
    assert_eq!(residue(y, 8) & 0xC0, 0xC0, "y={y}");
    assert!(y >= 192, "y={y}");
}

// ===========================================================================
// Shape 7: `x = bv2nat(bvlshr (int2bv 32 y) (int2bv 32 s))`.
// ===========================================================================

const LSHR: &str = r#"
    (set-logic ALL)
    (declare-const x Int) (declare-const y Int) (declare-const s Int)
    (assert (<= 0 y)) (assert (< y 4294967296))
    (assert (<= 0 s)) (assert (< s 32))
    (assert (= x (bv2nat (bvlshr ((_ int2bv 32) y) ((_ int2bv 32) s)))))
"#;

/// `256 >> 4 = 16`, not 17.
#[test]
#[timeout(60_000)]
fn lshr_pinned_operands() {
    let sat = format!("{LSHR} (assert (= y 256)) (assert (= s 4)) (assert (= x 16)) (check-sat)");
    assert_eq!(verdict(&sat), "sat");
    let unsat = format!("{LSHR} (assert (= y 256)) (assert (= s 4)) (assert (= x 17)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
}

/// A logical right shift never grows its operand.
#[test]
#[timeout(60_000)]
fn lshr_never_exceeds_operand_unsat() {
    let smt = format!("{LSHR} (assert (> x y)) (check-sat)");
    assert_eq!(verdict(&smt), "unsat");
}

// ===========================================================================
// Shape 8: the bridged value inside 64-bit arithmetic (width selection must
// clear the sums, not just the operands).
// ===========================================================================

const AND64_ARITH: &str = r#"
    (set-logic ALL)
    (declare-const a Int) (declare-const b Int) (declare-const s Int)
    (assert (<= 0 a)) (assert (< a 18446744073709551616))
    (assert (<= 0 b)) (assert (< b 18446744073709551616))
"#;

/// `a & b <= a + b` and `a | b >= a` for every pair of u64 values.
#[test]
#[timeout(60_000)]
fn and_or_64_arithmetic_bounds_unsat() {
    let and = format!(
        "{AND64_ARITH} (assert (= s (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) b))))) \
         (assert (> s (+ a b))) (check-sat)"
    );
    assert_eq!(verdict(&and), "unsat");
    let or = format!(
        "{AND64_ARITH} (assert (= s (bv2nat (bvor ((_ int2bv 64) a) ((_ int2bv 64) b))))) \
         (assert (< s a)) (check-sat)"
    );
    assert_eq!(verdict(&or), "unsat");
}

/// `3 & 7 = 3`: `s + 1 = a + 1` holds (sat); `s = a + b` does not (unsat).
#[test]
#[timeout(60_000)]
fn and64_arithmetic_pinned_operands() {
    let def = "(assert (= s (bv2nat (bvand ((_ int2bv 64) a) ((_ int2bv 64) b)))))";
    let sat = format!(
        "{AND64_ARITH} {def} (assert (= (+ s 1) (+ a 1))) (assert (= a 3)) (assert (= b 7)) \
         (check-sat) (get-model)"
    );
    let (v, lines) = run(&sat);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "s"), 3);
    let unsat = format!(
        "{AND64_ARITH} {def} (assert (= s (+ a b))) (assert (= a 3)) (assert (= b 3)) (check-sat)"
    );
    assert_eq!(verdict(&unsat), "unsat");
}

// ===========================================================================
// Signed bounds: a negative Int-lifted local through `int2bv`.
// ===========================================================================

#[test]
#[timeout(60_000)]
fn signed_bounded_source_modular_conversion() {
    let base = r#"
        (set-logic ALL)
        (declare-const x Int) (declare-const y Int)
        (assert (<= (- 128) y)) (assert (< y 128))
        (assert (= x (bv2nat ((_ int2bv 8) y))))
    "#;
    let sat = format!("{base} (assert (= y (- 1))) (check-sat) (get-model)");
    let (v, lines) = run(&sat);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "x"), 255);
    let unsat = format!("{base} (assert (= y (- 1))) (assert (= x 1)) (check-sat)");
    assert_eq!(verdict(&unsat), "unsat");
    // Backward: `x = 255` with a signed byte source forces `y = -1`.
    let back = format!("{base} (assert (= x 255)) (check-sat) (get-model)");
    let (v, lines) = run(&back);
    assert_eq!(v, "sat", "{lines:#?}");
    assert_eq!(model_int(&lines, "y"), -1);
}

/// SOUNDNESS: an unbounded Int with an arithmetic occurrence is outside the
/// blaster's fragment; the bridge must not answer `unsat` for a satisfiable
/// query it cannot decide. (`y = 300`, `x = 44` is a real model.)
#[test]
#[timeout(60_000)]
fn out_of_fragment_query_is_never_refuted() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int) (declare-const y Int)
        (assert (= x (bv2nat ((_ int2bv 8) y))))
        (assert (< x y))
        (check-sat)
    "#;
    assert_ne!(verdict(smt), "unsat");
}
