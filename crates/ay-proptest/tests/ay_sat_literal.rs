// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{Literal, Variable};
use proptest::prelude::*;

proptest! {
    /// Negation is involutive
    #[test]
    fn prop_negation_involutive(var_idx in 0u32..100_000) {
        let var = Variable::new(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        prop_assert_eq!(pos.negated().negated(), pos);
        prop_assert_eq!(neg.negated().negated(), neg);
    }

    /// Variable extraction is correct
    #[test]
    fn prop_variable_extraction(var_idx in 0u32..100_000) {
        let var = Variable::new(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        prop_assert_eq!(pos.variable(), var);
        prop_assert_eq!(neg.variable(), var);
    }

    /// Polarity is correct
    #[test]
    fn prop_polarity_correct(var_idx in 0u32..100_000) {
        let var = Variable::new(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        prop_assert!(pos.is_positive());
        prop_assert!(!neg.is_positive());
    }

    /// Positive and negative are distinct
    #[test]
    fn prop_polarity_distinct(var_idx in 0u32..100_000) {
        let var = Variable::new(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        prop_assert_ne!(pos, neg);
        prop_assert_eq!(pos.negated(), neg);
        prop_assert_eq!(neg.negated(), pos);
    }

    /// Index is consistent
    #[test]
    fn prop_index_consistent(var_idx in 0u32..100_000) {
        let var = Variable::new(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        prop_assert_eq!(pos.index(), (var_idx as usize) * 2);
        prop_assert_eq!(neg.index(), (var_idx as usize) * 2 + 1);
    }
}

#[test]
fn test_literal_basic() {
    let var = Variable::new(5);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
    assert_eq!(pos.negated(), neg);
    assert_eq!(neg.negated(), pos);
}

#[test]
fn test_variable_zero() {
    let var = Variable::new(0);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.raw(), 0);
    assert_eq!(neg.raw(), 1);
    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
}

#[test]
fn test_from_dimacs() {
    assert_eq!(Literal::from_dimacs(1), Literal::positive(Variable::new(0)));
    assert_eq!(
        Literal::from_dimacs(-1),
        Literal::negative(Variable::new(0))
    );
    assert_eq!(Literal::from_dimacs(5), Literal::positive(Variable::new(4)));
    assert_eq!(
        Literal::from_dimacs(-5),
        Literal::negative(Variable::new(4))
    );
}

#[test]
#[should_panic(expected = "DIMACS uses literal 0 as clause terminator")]
fn test_from_dimacs_panics_on_zero() {
    let _ = Literal::from_dimacs(0);
}

#[test]
fn test_from_i32() {
    // From<i32> uses absolute value directly as variable ID (no -1 offset)
    assert_eq!(Literal::from(1), Literal::positive(Variable::new(1)));
    assert_eq!(Literal::from(-1), Literal::negative(Variable::new(1)));
    assert_eq!(Literal::from(5), Literal::positive(Variable::new(5)));
    assert_eq!(Literal::from(-5), Literal::negative(Variable::new(5)));
}

#[test]
#[should_panic(expected = "literal 0 has no valid interpretation")]
fn test_from_i32_panics_on_zero() {
    let _ = Literal::from(0);
}

// -- Overflow boundary tests (#4474) --

#[test]
fn test_literal_max_safe_variable() {
    // Variable(i32::MAX as u32) = Variable(2_147_483_647) is the max for
    // literal encoding (2 * 2^31-1 = u32::MAX - 1, fits in u32).
    let var = Variable::new(i32::MAX as u32);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.variable(), var);
    assert_eq!(neg.variable(), var);
    assert!(pos.is_positive());
    assert!(!neg.is_positive());
}

#[test]
fn test_to_dimacs_max_safe_variable() {
    // Variable(i32::MAX as u32 - 1) -> DIMACS i32::MAX
    let var = Variable::new(i32::MAX as u32 - 1);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    assert_eq!(pos.to_dimacs(), i32::MAX);
    assert_eq!(neg.to_dimacs(), -i32::MAX);
}

#[test]
#[should_panic(expected = "maximum literal/DIMACS encoding index")]
fn test_positive_panics_on_overflow_variable() {
    let _ = Literal::positive(Variable::new(i32::MAX as u32 + 1));
}

#[test]
#[should_panic(expected = "maximum literal/DIMACS encoding index")]
fn test_negative_panics_on_overflow_variable() {
    let _ = Literal::negative(Variable::new(i32::MAX as u32 + 1));
}

#[test]
#[should_panic(expected = "DIMACS i32 encoding range")]
fn test_to_dimacs_panics_on_overflow() {
    // Variable(i32::MAX as u32) -> DIMACS would be i32::MAX + 1, overflow
    let lit = Literal::positive(Variable::new(i32::MAX as u32));
    let _ = lit.to_dimacs();
}

// -- Release-mode overflow enforcement (#4474) --
// These tests verify the assert! (not debug_assert!) fires in all profiles.

#[test]
#[should_panic(expected = "exceeds maximum literal/DIMACS encoding index")]
fn test_positive_panics_on_overlimit_variable() {
    // Variable(i32::MAX as u32 + 1) = 2^31: encoding 2*2^31 overflows u32.
    // Must panic in both debug AND release builds.
    let _ = Literal::positive(Variable::new(i32::MAX as u32 + 1));
}

#[test]
#[should_panic(expected = "exceeds maximum literal/DIMACS encoding index")]
fn test_negative_panics_on_overlimit_variable() {
    let _ = Literal::negative(Variable::new(i32::MAX as u32 + 1));
}

#[test]
#[should_panic(expected = "exceeds maximum literal/DIMACS encoding index")]
fn test_positive_panics_on_u32_max() {
    // Variable(u32::MAX) is far beyond the limit.
    let _ = Literal::positive(Variable::new(u32::MAX));
}

#[test]
#[should_panic(expected = "exceeds maximum literal/DIMACS encoding index")]
fn test_negative_panics_on_u32_max() {
    let _ = Literal::negative(Variable::new(u32::MAX));
}

// -- from_index() roundtrip tests (#4474) --

#[test]
fn test_from_index_roundtrip_max_safe_variable() {
    // The max-safe variable for binary proof encoding is i32::MAX - 1.
    let var = Variable::new(i32::MAX as u32 - 1);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    // Roundtrip through index/from_index preserves variable and polarity
    let pos_rt = Literal::from_index(pos.index());
    let neg_rt = Literal::from_index(neg.index());

    assert_eq!(pos_rt.variable(), var);
    assert_eq!(neg_rt.variable(), var);
    assert!(pos_rt.is_positive());
    assert!(!neg_rt.is_positive());
}

#[test]
fn test_from_index_bypasses_constructor_check() {
    // from_index() does NOT enforce the variable range limit.
    // This is by design for internal use, but callers must ensure
    // the resulting literal is only used with checked proof writers.
    let lit = Literal::from_index(u32::MAX as usize);
    // Should NOT panic because from_index has no assert.
    assert_eq!(lit.variable(), Variable::new(u32::MAX >> 1));
    assert!(!lit.is_positive()); // bit 0 is 1
}
