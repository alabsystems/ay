// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

// =========================================================================
// Bitvector comparison tests
// =========================================================================

#[test]
fn test_bvult_constant_folding() {
    let mut store = TermStore::new();

    // 1 < 2 = true (unsigned)
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvult(one, two);
    assert_eq!(result, store.true_term());

    // 2 < 1 = false (unsigned)
    let result2 = store.mk_bvult(two, one);
    assert_eq!(result2, store.false_term());

    // 0xFF < 0x01 = false (unsigned: 255 < 1 is false)
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let result3 = store.mk_bvult(ff, one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvult_reflexivity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x < x = false
    let result = store.mk_bvult(x, x);
    assert_eq!(result, store.false_term());

    // x < 0 = false (nothing is less than 0 unsigned)
    let result2 = store.mk_bvult(x, zero);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvule_constant_folding() {
    let mut store = TermStore::new();

    // 1 <= 2 = true
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let two = store.mk_bitvec(BigInt::from(2), 8);
    let result = store.mk_bvule(one, two);
    assert_eq!(result, store.true_term());

    // 2 <= 2 = true
    let result2 = store.mk_bvule(two, two);
    assert_eq!(result2, store.true_term());

    // 2 <= 1 = false
    let result3 = store.mk_bvule(two, one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvule_reflexivity_and_zero() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // x <= x = true
    let result = store.mk_bvule(x, x);
    assert_eq!(result, store.true_term());

    // 0 <= x = true (0 is <= everything unsigned)
    let result2 = store.mk_bvule(zero, x);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_bvugt_normalization() {
    let mut store = TermStore::new();

    // bvugt(a, b) should normalize to bvult(b, a)
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);

    // 5 > 3 = true
    let result = store.mk_bvugt(a, b);
    assert_eq!(result, store.true_term());

    // 3 > 5 = false
    let result2 = store.mk_bvugt(b, a);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvuge_normalization() {
    let mut store = TermStore::new();

    // bvuge(a, b) should normalize to bvule(b, a)
    let a = store.mk_bitvec(BigInt::from(5), 8);
    let b = store.mk_bitvec(BigInt::from(3), 8);

    // 5 >= 3 = true
    let result = store.mk_bvuge(a, b);
    assert_eq!(result, store.true_term());

    // 5 >= 5 = true
    let result2 = store.mk_bvuge(a, a);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_bvslt_constant_folding() {
    let mut store = TermStore::new();

    // Signed comparison: -1 < 1 is true
    // In 8-bit two's complement, 0xFF = -1
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvslt(neg_one, one);
    assert_eq!(result, store.true_term());

    // Signed: 1 < -1 is false
    let result2 = store.mk_bvslt(one, neg_one);
    assert_eq!(result2, store.false_term());

    // Signed: -128 (0x80) < 127 (0x7F) is true
    let min_val = store.mk_bitvec(BigInt::from(0x80), 8);
    let max_val = store.mk_bitvec(BigInt::from(0x7F), 8);
    let result3 = store.mk_bvslt(min_val, max_val);
    assert_eq!(result3, store.true_term());

    // Signed: 127 < -128 is false
    let result4 = store.mk_bvslt(max_val, min_val);
    assert_eq!(result4, store.false_term());
}

#[test]
fn test_bvslt_reflexivity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));

    // x < x = false
    let result = store.mk_bvslt(x, x);
    assert_eq!(result, store.false_term());
}

#[test]
fn test_bvsle_constant_folding() {
    let mut store = TermStore::new();

    // Signed: -1 <= 1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsle(neg_one, one);
    assert_eq!(result, store.true_term());

    // Signed: -1 <= -1 is true
    let result2 = store.mk_bvsle(neg_one, neg_one);
    assert_eq!(result2, store.true_term());

    // Signed: 1 <= -1 is false
    let result3 = store.mk_bvsle(one, neg_one);
    assert_eq!(result3, store.false_term());
}

#[test]
fn test_bvsle_reflexivity() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));

    // x <= x = true
    let result = store.mk_bvsle(x, x);
    assert_eq!(result, store.true_term());
}

#[test]
fn test_bvsgt_normalization() {
    let mut store = TermStore::new();

    // bvsgt(a, b) normalizes to bvslt(b, a)
    // Signed: 1 > -1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsgt(one, neg_one);
    assert_eq!(result, store.true_term());

    // Signed: -1 > 1 is false
    let result2 = store.mk_bvsgt(neg_one, one);
    assert_eq!(result2, store.false_term());
}

#[test]
fn test_bvsge_normalization() {
    let mut store = TermStore::new();

    // bvsge(a, b) normalizes to bvsle(b, a)
    // Signed: 1 >= -1 is true
    let neg_one = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);
    let result = store.mk_bvsge(one, neg_one);
    assert_eq!(result, store.true_term());

    // Signed: 1 >= 1 is true
    let result2 = store.mk_bvsge(one, one);
    assert_eq!(result2, store.true_term());
}

#[test]
fn test_signed_vs_unsigned_comparison() {
    let mut store = TermStore::new();

    // 0xFF: unsigned = 255, signed = -1
    let ff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let one = store.mk_bitvec(BigInt::from(1), 8);

    // Unsigned: 255 < 1 is false
    let ult_result = store.mk_bvult(ff, one);
    assert_eq!(ult_result, store.false_term());

    // Signed: -1 < 1 is true
    let slt_result = store.mk_bvslt(ff, one);
    assert_eq!(slt_result, store.true_term());
}

// =========================================================================
// Fixed-width RANGE-ENDPOINT folds: the all-ones / signed-extreme duals of
// the existing zero rules.
//
// Every assertion below is a validity (or a refutability) of the theory of
// fixed-width bitvectors, so each fold is an EQUIVALENCE — model-preserving in
// both directions, so UNSAT stays UNSAT and SAT stays SAT. The
// `must_not_over_reach` / `cross_width` tests are the adversarial half: they
// pin the exact over-reaches that would turn these equivalences into false
// proofs.
// =========================================================================

#[test]
fn test_bvule_unsigned_max_upper_bound_folds() {
    let mut store = TermStore::new();
    let t = store.true_term();

    let x = store.mk_var("x", Sort::bitvec(8));
    let umax = store.mk_bitvec(BigInt::from(0xFF), 8);

    // x <=u 0xFF = true (all-ones bounds every 8-bit value)
    let result = store.mk_bvule(x, umax);
    assert_eq!(result, t);

    // bvuge(0xFF, x) normalizes to bvule(x, 0xFF) = true
    let result2 = store.mk_bvuge(umax, x);
    assert_eq!(result2, t);

    // 64-bit: the width the Trust/model-checker-consumer panic-freedom encoding emits, as
    // the second half of every `0 <=u x /\ x <=u UMAX` range-fact pair.
    let y = store.mk_var("y", Sort::bitvec(64));
    let umax64 = store.mk_bitvec(BigInt::from(u64::MAX), 64);
    let result3 = store.mk_bvule(y, umax64);
    assert_eq!(result3, t);
}

#[test]
fn test_bvult_unsigned_max_lower_bound_folds() {
    let mut store = TermStore::new();
    let f = store.false_term();

    let x = store.mk_var("x", Sort::bitvec(8));
    let umax = store.mk_bitvec(BigInt::from(0xFF), 8);

    // 0xFF <u x = false (nothing exceeds all-ones)
    let result = store.mk_bvult(umax, x);
    assert_eq!(result, f);

    // bvugt(x, 0xFF) normalizes to bvult(0xFF, x) = false
    let result2 = store.mk_bvugt(x, umax);
    assert_eq!(result2, f);
}

#[test]
fn test_bvsle_signed_extremes_fold() {
    let mut store = TermStore::new();
    let t = store.true_term();

    let x = store.mk_var("x", Sort::bitvec(8));
    let smax = store.mk_bitvec(BigInt::from(0x7F), 8); // +127
    let smin = store.mk_bitvec(BigInt::from(0x80), 8); // -128

    let r1 = store.mk_bvsle(x, smax); // x <=s 127
    assert_eq!(r1, t);
    let r2 = store.mk_bvsle(smin, x); // -128 <=s x
    assert_eq!(r2, t);
    let r3 = store.mk_bvsge(smax, x); // normalizes to bvsle(x, 127)
    assert_eq!(r3, t);
}

#[test]
fn test_bvslt_signed_extremes_fold() {
    let mut store = TermStore::new();
    let f = store.false_term();

    let x = store.mk_var("x", Sort::bitvec(8));
    let smax = store.mk_bitvec(BigInt::from(0x7F), 8); // +127
    let smin = store.mk_bitvec(BigInt::from(0x80), 8); // -128

    let r1 = store.mk_bvslt(x, smin); // x <s -128
    assert_eq!(r1, f);
    let r2 = store.mk_bvslt(smax, x); // 127 <s x
    assert_eq!(r2, f);
    let r3 = store.mk_bvsgt(x, smax); // normalizes to bvslt(127, x)
    assert_eq!(r3, f);
}

#[test]
fn test_width_one_range_endpoints_fold() {
    let mut store = TermStore::new();
    let t = store.true_term();
    let f = store.false_term();

    let b = store.mk_var("b", Sort::bitvec(1));
    let zero = store.mk_bitvec(BigInt::from(0), 1); // unsigned 0, signed  0 == SMAX
    let one = store.mk_bitvec(BigInt::from(1), 1); //  unsigned 1, signed -1 == SMIN

    // Unsigned range of a 1-bit vector is [0, 1].
    let r = store.mk_bvule(b, one);
    assert_eq!(r, t);
    let r = store.mk_bvult(one, b);
    assert_eq!(r, f);
    // Signed range of a 1-bit vector is [-1, 0]: SMAX = 0b0, SMIN = 0b1.
    let r = store.mk_bvsle(b, zero);
    assert_eq!(r, t);
    let r = store.mk_bvsle(one, b);
    assert_eq!(r, t);
    let r = store.mk_bvslt(b, one);
    assert_eq!(r, f);
    let r = store.mk_bvslt(zero, b);
    assert_eq!(r, f);
}

#[test]
fn test_range_endpoint_folds_must_not_over_reach() {
    let mut store = TermStore::new();
    let t = store.true_term();
    let f = store.false_term();

    let x = store.mk_var("x", Sort::bitvec(8));
    let umax = store.mk_bitvec(BigInt::from(0xFF), 8);
    let near_max = store.mk_bitvec(BigInt::from(0xFE), 8);
    let smax = store.mk_bitvec(BigInt::from(0x7F), 8);
    let smin = store.mk_bitvec(BigInt::from(0x80), 8);
    let zero = store.mk_bitvec(BigInt::from(0), 8);

    // `x <=u 0xFE` is both satisfiable and falsifiable — must stay symbolic.
    let r = store.mk_bvule(x, near_max);
    assert_ne!(r, t, "bvule(x, UMAX-1) must not fold to true");
    assert_ne!(r, f, "bvule(x, UMAX-1) must not fold to false");

    // FALSE-PROOF TRAP: all-ones is signed -1, NOT the signed maximum.
    // `x <=s -1` is false for x = 1, so it must not fold to true.
    let r = store.mk_bvsle(x, umax);
    assert_ne!(
        r, t,
        "bvsle(x, all-ones) must not fold: all-ones is signed -1"
    );
    assert_ne!(r, f);

    // Dual trap: `-1 <s x` is falsifiable (x = -1) and satisfiable (x = 0).
    let r = store.mk_bvslt(umax, x);
    assert_ne!(r, t);
    assert_ne!(
        r, f,
        "bvslt(all-ones, x) must not fold: all-ones is signed -1"
    );

    // `x <s 0` is satisfiable for negative x and false for x = 1: the UNSIGNED
    // zero endpoint is not a SIGNED endpoint.
    let r = store.mk_bvslt(x, zero);
    assert_ne!(r, t);
    assert_ne!(
        r, f,
        "bvslt(x, 0) must not fold: 0 is not the signed minimum"
    );

    // And the signed endpoints are not unsigned endpoints: `x <=u 0x7F` is
    // falsifiable (x = 0xFF), `0x80 <=u x` is falsifiable (x = 0).
    let r = store.mk_bvule(x, smax);
    assert_ne!(
        r, t,
        "bvule(x, SMAX) must not fold: SMAX is not the unsigned max"
    );
    assert_ne!(r, f);
    let r = store.mk_bvule(smin, x);
    assert_ne!(
        r, t,
        "bvule(SMIN, x) must not fold: SMIN is not unsigned zero"
    );
    assert_ne!(r, f);
}

// NOTE: the cross-width guard inside these rules cannot be exercised by a test
// here — `mk_bvult`/`mk_bvule`/`mk_bvslt`/`mk_bvsle` all carry a
// `debug_assert!` that rejects mismatched operand sorts before any folding
// runs, so a test build aborts first. The `bv_const_is` width check is the
// RELEASE-build backstop for that already-rejected case, and it is written to
// fail closed (decline to fold) rather than to trust the constant's own width.
