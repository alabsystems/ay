// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Literal and variable representation

/// Clause represented with signed integer literals.
///
/// Positive integers encode positive literals and negative integers encode
/// negated literals. Variable identifiers are taken directly from absolute
/// values (no DIMACS 1-based adjustment).
pub type SignedClause = Vec<i32>;

/// A variable identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Variable(pub(crate) u32);

/// A literal (variable with polarity)
///
/// Encoded as: positive literal = 2*var, negative literal = 2*var + 1
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, bytemuck::Pod, bytemuck::Zeroable,
)]
#[repr(transparent)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Literal(pub(crate) u32);

/// Largest variable index representable in both internal literal encoding and
/// DIMACS i32 text/binary proof formats.
const MAX_LITERAL_VARIABLE_INDEX: u32 = i32::MAX as u32;

impl Literal {
    #[inline]
    fn assert_encodable_variable(var: Variable) {
        assert!(
            var.0 <= MAX_LITERAL_VARIABLE_INDEX,
            "BUG: Variable({}) exceeds maximum literal/DIMACS encoding index ({})",
            var.0,
            MAX_LITERAL_VARIABLE_INDEX,
        );
    }

    /// Create a positive literal
    ///
    /// # Panics
    ///
    /// Panics when `var.0 > i32::MAX as u32` to avoid silent wrap in release
    /// builds and keep literal encoding compatible with DIMACS proof formats.
    #[inline]
    pub fn positive(var: Variable) -> Self {
        Self::assert_encodable_variable(var);
        Self(var.0 << 1)
    }

    /// Create a negative literal
    ///
    /// # Panics
    ///
    /// Panics when `var.0 > i32::MAX as u32` to avoid silent wrap in release
    /// builds and keep literal encoding compatible with DIMACS proof formats.
    #[inline]
    pub fn negative(var: Variable) -> Self {
        Self::assert_encodable_variable(var);
        Self((var.0 << 1) | 1)
    }

    /// Get the variable
    #[inline]
    pub fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    /// Check if positive
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Get the negation
    #[inline]
    pub fn negated(self) -> Self {
        Self(self.0 ^ 1)
    }

    /// Get the raw packed encoding value
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Get the index for watched literal arrays
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Create a literal from its index
    ///
    /// This is the inverse of `index()`.
    #[inline]
    pub fn from_index(idx: usize) -> Self {
        Self(idx as u32)
    }

    /// Polarity as `i8`: `1` for positive, `-1` for negative.
    #[inline]
    pub fn sign_i8(self) -> i8 {
        if self.is_positive() {
            1
        } else {
            -1
        }
    }

    /// Create a literal from a DIMACS-style signed integer.
    ///
    /// DIMACS literals are 1-indexed by variable ID and use sign for polarity.
    /// Literal `0` is reserved as the clause terminator and is invalid here.
    #[inline]
    pub fn from_dimacs(dimacs_lit: i32) -> Self {
        assert_ne!(dimacs_lit, 0, "DIMACS uses literal 0 as clause terminator");
        let var = Variable(dimacs_lit.unsigned_abs() - 1);
        if dimacs_lit > 0 {
            Self::positive(var)
        } else {
            Self::negative(var)
        }
    }

    /// Convert to a DIMACS-style signed integer (inverse of `from_dimacs`).
    ///
    /// # Panics
    ///
    /// Panics if the variable index exceeds the DIMACS i32 encoding range
    /// (variable index must be < `i32::MAX as u32`).
    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let var_idx = self.variable().0;
        let var_id = i32::try_from(var_idx)
            .ok()
            .and_then(|v| v.checked_add(1))
            .expect("BUG: variable index exceeds DIMACS i32 encoding range");
        if self.is_positive() {
            var_id
        } else {
            -var_id
        }
    }
}

impl From<i32> for Literal {
    /// Convert a signed integer to a literal.
    ///
    /// The absolute value is used as the variable ID and the sign determines
    /// polarity: positive → positive literal, negative → negative literal.
    ///
    /// Unlike [`Literal::from_dimacs`], this does **not** subtract 1 from the
    /// variable ID. Use this for internal variable numbering; use `from_dimacs`
    /// for DIMACS-format input where variables are 1-indexed.
    ///
    /// # Panics
    ///
    /// Panics if `lit` is 0 (no valid literal interpretation).
    #[inline]
    fn from(lit: i32) -> Self {
        assert_ne!(lit, 0, "literal 0 has no valid interpretation");
        let var = Variable(lit.unsigned_abs());
        if lit > 0 {
            Self::positive(var)
        } else {
            Self::negative(var)
        }
    }
}

impl Variable {
    /// Create a new variable from a raw identifier
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw variable identifier
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }

    /// Get the index (convenience for array indexing)
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

// ============================================================================
// Kani Verification Harnesses
// ============================================================================

#[cfg(kani)]
mod verification {
    use super::*;

    /// Negation is involutive: negating twice returns the original literal
    #[kani::proof]
    fn literal_negation_involutive() {
        let lit: Literal = kani::any();
        // Bound for tractability (half of u32::MAX due to encoding)
        kani::assume(lit.0 < 1_000_000);
        assert_eq!(lit.negated().negated(), lit);
    }

    /// Variable roundtrip: creating positive/negative literals preserves variable
    #[kani::proof]
    fn literal_variable_roundtrip() {
        let var: Variable = kani::any();
        // Bound to prevent overflow in shift operation
        kani::assume(var.0 < 500_000);

        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        assert_eq!(pos.variable(), var);
        assert_eq!(neg.variable(), var);
        assert!(pos.is_positive());
        assert!(!neg.is_positive());
    }

    /// Encoding uniqueness: different variables have different literal encodings
    #[kani::proof]
    fn literal_encoding_unique() {
        let var1: Variable = kani::any();
        let var2: Variable = kani::any();
        kani::assume(var1.0 < 500_000 && var2.0 < 500_000);

        let pos1 = Literal::positive(var1);
        let pos2 = Literal::positive(var2);

        // Same encoding implies same variable
        if pos1.0 == pos2.0 {
            assert_eq!(var1, var2);
        }
    }

    /// Positive and negative literals for the same variable are different
    #[kani::proof]
    fn literal_polarity_distinct() {
        let var: Variable = kani::any();
        kani::assume(var.0 < 500_000);

        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        assert_ne!(pos, neg);
        assert_eq!(pos.negated(), neg);
        assert_eq!(neg.negated(), pos);
    }

    /// Index is consistent with encoding
    #[kani::proof]
    fn literal_index_consistent() {
        let var: Variable = kani::any();
        kani::assume(var.0 < 500_000);

        let pos = Literal::positive(var);
        let neg = Literal::negative(var);

        // Indices should be consecutive: pos = 2*var, neg = 2*var + 1
        assert_eq!(pos.index(), (var.0 as usize) * 2);
        assert_eq!(neg.index(), (var.0 as usize) * 2 + 1);
    }
}
