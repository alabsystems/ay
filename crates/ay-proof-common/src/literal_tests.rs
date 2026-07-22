// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_literal_roundtrip() {
    for d in [-5, -1, 1, 3, 100] {
        let lit = Literal::from_dimacs(d);
        assert_eq!(lit.to_dimacs(), d);
    }
}

#[test]
fn test_negation() {
    let lit = Literal::from_dimacs(3);
    assert!(lit.is_positive());
    let neg = lit.negated();
    assert!(!neg.is_positive());
    assert_eq!(neg.variable(), lit.variable());
    assert_eq!(neg.negated(), lit);
}

#[test]
fn test_index_layout() {
    let pos = Literal::positive(Variable::new(5));
    let neg = Literal::negative(Variable::new(5));
    assert_eq!(pos.index(), 10);
    assert_eq!(neg.index(), 11);
}

#[test]
fn test_from_index_roundtrip() {
    // from_index is the inverse of index() — verify the roundtrip.
    for d in [-5, -1, 1, 3, 100] {
        let lit = Literal::from_dimacs(d);
        let reconstructed = Literal::from_index(lit.index());
        assert_eq!(reconstructed, lit);
        assert_eq!(reconstructed.is_positive(), lit.is_positive());
        assert_eq!(reconstructed.variable(), lit.variable());
    }
}

#[test]
fn test_max_var_boundary() {
    // MAX_VAR should be representable without overflow.
    let var = Variable::new(Literal::MAX_VAR);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
}

#[test]
#[should_panic(expected = "exceeds Literal::MAX_VAR")]
fn test_overflow_variable_panics() {
    // Variable > MAX_VAR triggers assert! in both debug and release.
    let var = Variable::new(Literal::MAX_VAR + 1);
    let _ = Literal::positive(var);
}

/// Verifies that the overflow guard in Literal::positive/negative is a
/// runtime assert (not debug_assert), catching overflow in release builds.
/// Previously this was debug_assert only — fixed by promoting to assert!.
#[test]
fn test_max_var_guard_is_always_on() {
    assert_eq!(Literal::MAX_VAR, (1u32 << 31) - 1);
    let var = Variable::new(Literal::MAX_VAR);
    let lit = Literal::positive(var);
    assert_eq!(lit.variable(), var);
    // The overflow case (MAX_VAR + 1) is tested in
    // test_overflow_variable_panics — now catches in BOTH debug and release.
}

#[test]
#[should_panic(expected = "variable ID too large for DIMACS")]
fn test_to_dimacs_overflow_panics() {
    // MAX_VAR = 2^31 - 1 = 2_147_483_647. DIMACS is 1-indexed, so
    // to_dimacs needs var_id + 1 = 2_147_483_648, which overflows i32.
    let var = Variable::new(Literal::MAX_VAR);
    let lit = Literal::positive(var);
    let _ = lit.to_dimacs();
}

#[test]
fn test_to_dimacs_i64_handles_max_var() {
    // to_dimacs_i64 must not panic even for MAX_VAR (where to_dimacs panics).
    let var = Variable::new(Literal::MAX_VAR);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);
    assert_eq!(pos.to_dimacs_i64(), 2_147_483_648i64);
    assert_eq!(neg.to_dimacs_i64(), -2_147_483_648i64);
}

#[test]
fn test_to_dimacs_i64_roundtrip_small() {
    for d in [-5i32, -1, 1, 3, 100] {
        let lit = Literal::from_dimacs(d);
        assert_eq!(lit.to_dimacs_i64(), i64::from(d));
    }
}

#[test]
fn test_display_uses_i64() {
    // Display must not panic on MAX_VAR extension variables.
    let var = Variable::new(Literal::MAX_VAR);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);
    assert_eq!(format!("{pos}"), "2147483648");
    assert_eq!(format!("{neg}"), "-2147483648");
}

#[test]
fn test_display_small_literals() {
    let lit = Literal::from_dimacs(3);
    assert_eq!(format!("{lit}"), "3");
    let neg = Literal::from_dimacs(-1);
    assert_eq!(format!("{neg}"), "-1");
}

/// Dense-range twin of the Kani harnesses in `literal.rs` (`mod verification`).
/// Checks every encoding soundness invariant — variable/polarity round-trip,
/// negation involution, index round-trip, and the proof-checker-critical DIMACS
/// round-trip — over a dense range of variables and signed literals. This runs
/// locally (validating the property expressions and catching any real encoding
/// regression); the `#[cfg(kani)]` harnesses prove the same invariants over the
/// full bounded input space via model-checker-consumer/Kani.
#[test]
fn test_encoding_invariants_dense() {
    for v in 0u32..=20_000 {
        let var = Variable::new(v);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);
        // variable + polarity round-trip
        assert_eq!(pos.variable(), var);
        assert_eq!(neg.variable(), var);
        assert!(pos.is_positive());
        assert!(!neg.is_positive());
        // negation is involutive, swaps polarity, preserves the variable
        assert_eq!(pos.negated(), neg);
        assert_eq!(neg.negated(), pos);
        assert_eq!(pos.negated().negated(), pos);
        assert_eq!(pos.negated().variable(), var);
        // compact index layout + round-trip
        assert_eq!(pos.index(), 2 * v as usize);
        assert_eq!(neg.index(), 2 * v as usize + 1);
        assert_eq!(Literal::from_index(pos.index()), pos);
        assert_eq!(Literal::from_index(neg.index()), neg);
    }
    // DIMACS round-trip — soundness-critical for DRAT/LRAT proof parsing.
    for d in (-20_000i32..=20_000).filter(|&d| d != 0) {
        let lit = Literal::from_dimacs(d);
        assert_eq!(lit.to_dimacs(), d, "to_dimacs must invert from_dimacs");
        assert_eq!(lit.to_dimacs_i64(), i64::from(d));
        assert_eq!(lit.is_positive(), d > 0);
    }
}
