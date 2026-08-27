// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded proofs for the literal encoding.

use super::*;

/// Negation is involutive, swaps polarity, and preserves the variable.
#[kani::proof]
fn prove_negation_involutive() {
    let raw: u32 = kani::any();
    // index = 2*var(+1); bound keeps the encoding well within u32 + tractable.
    kani::assume(raw < (1 << 22));
    let lit = Literal::from_index(raw as usize);
    assert_eq!(lit.negated().negated(), lit);
    assert_eq!(lit.negated().variable(), lit.variable());
    assert!(lit.negated().is_positive() != lit.is_positive());
}

/// `positive`/`negative` preserve the variable and set the correct polarity,
/// and are exact negations of each other.
#[kani::proof]
fn prove_variable_polarity_roundtrip() {
    let v: u32 = kani::any();
    kani::assume(v <= (1 << 21)); // << MAX_VAR so the `<< 1` stays in range
    let var = Variable::new(v);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);
    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
    assert_eq!(pos.negated(), neg);
    assert_eq!(neg.negated(), pos);
}

/// DIMACS round-trip: `from_dimacs` then `to_dimacs`/`to_dimacs_i64` recovers
/// the signed literal exactly, with correct polarity. The soundness-critical
/// property for DRAT/LRAT proof parsing.
#[kani::proof]
fn prove_dimacs_roundtrip() {
    let d: i32 = kani::any();
    kani::assume(d != 0);
    // |d|-1 is the 0-indexed var; bound below MAX_VAR and i32::MAX-1.
    kani::assume(d > -(1 << 21) && d < (1 << 21));
    let lit = Literal::from_dimacs(d);
    assert_eq!(lit.to_dimacs(), d);
    assert_eq!(lit.to_dimacs_i64(), i64::from(d));
    assert_eq!(lit.is_positive(), d > 0);
}

/// `from_index` is the exact inverse of `index`.
#[kani::proof]
fn prove_index_roundtrip() {
    let raw: u32 = kani::any();
    kani::assume(raw < (1 << 22));
    let lit = Literal::from_index(raw as usize);
    assert_eq!(lit.index(), raw as usize);
    assert_eq!(Literal::from_index(lit.index()), lit);
}

/// The encoding is injective: distinct variables map to distinct literals.
#[kani::proof]
fn prove_encoding_injective() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a <= (1 << 21) && b <= (1 << 21));
    if Literal::positive(Variable::new(a)) == Literal::positive(Variable::new(b)) {
        assert_eq!(a, b);
    }
}
