// Copyright 2026 Andrew Yates
// Standalone literal/variable types for SAT proof checkers.
// Encoding: positive = 2*var, negative = 2*var + 1. Zero-indexed internally.

#[allow(unused_imports)]
use crate::contracts::{ensures, requires};

/// A variable identifier (0-indexed internally).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Variable(u32);

impl Variable {
    /// Create a new variable from a raw 0-indexed identifier.
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw 0-indexed identifier.
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A literal (variable with polarity).
///
/// Encoded as: positive = 2*var, negative = 2*var + 1.
/// This compact encoding allows direct indexing into watch/assignment arrays.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Literal(u32);

impl Literal {
    /// Maximum variable index that can be represented without overflow.
    /// Variable indices >= 2^31 would cause the `<< 1` encoding to overflow u32.
    pub const MAX_VAR: u32 = (1 << 31) - 1;

    /// Create a positive literal for the given variable.
    #[inline]
    pub fn positive(var: Variable) -> Self {
        requires!(var.0 <= Self::MAX_VAR);
        assert!(
            var.0 <= Self::MAX_VAR,
            "variable {} exceeds Literal::MAX_VAR",
            var.0
        );
        let result = Self(var.0 << 1);
        ensures!(result.variable() == var);
        ensures!(result.is_positive());
        result
    }

    /// Create a negative literal for the given variable.
    #[inline]
    pub fn negative(var: Variable) -> Self {
        requires!(var.0 <= Self::MAX_VAR);
        assert!(
            var.0 <= Self::MAX_VAR,
            "variable {} exceeds Literal::MAX_VAR",
            var.0
        );
        let result = Self((var.0 << 1) | 1);
        ensures!(result.variable() == var);
        ensures!(!result.is_positive());
        result
    }

    /// Get the underlying variable.
    #[inline]
    pub fn variable(self) -> Variable {
        Variable(self.0 >> 1)
    }

    /// True if this literal has positive polarity.
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }

    /// Get the negation of this literal.
    #[inline]
    pub fn negated(self) -> Self {
        let result = Self(self.0 ^ 1);
        ensures!(result.variable() == self.variable());
        ensures!(result.is_positive() != self.is_positive());
        ensures!(result.negated() == self);
        result
    }

    /// Index into watch/assignment arrays (2 entries per variable).
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Create a literal from a raw index (inverse of `index()`).
    ///
    /// The index encodes both variable and polarity: `positive = 2*var`,
    /// `negative = 2*var + 1`. This enables zero-cost conversion between
    /// literal types that use the same encoding scheme.
    #[inline]
    pub fn from_index(idx: usize) -> Self {
        Self(idx as u32)
    }

    /// Create a literal from a DIMACS-style signed integer.
    ///
    /// DIMACS variables are 1-indexed. `from_dimacs(3)` → positive literal for
    /// internal variable 2. `from_dimacs(-1)` → negative literal for variable 0.
    #[inline]
    pub fn from_dimacs(dimacs: i32) -> Self {
        requires!(dimacs != 0);
        assert_ne!(dimacs, 0, "DIMACS literal 0 is a clause terminator");
        let var = Variable(dimacs.unsigned_abs() - 1);
        let result = if dimacs > 0 {
            Self::positive(var)
        } else {
            Self::negative(var)
        };
        ensures!(result.is_positive() == (dimacs > 0));
        result
    }

    /// Convert to DIMACS signed integer (inverse of `from_dimacs`).
    ///
    /// Panics if the variable ID exceeds `i32::MAX - 1` (2_147_483_646),
    /// which would cause the 1-indexed DIMACS representation to overflow.
    /// Use `to_dimacs_i64` or the `Display` impl for extension variables
    /// that may exceed this range.
    #[inline]
    pub fn to_dimacs(self) -> i32 {
        let raw = self.variable().id();
        let var_1indexed = i32::try_from(raw)
            .ok()
            .and_then(|v| v.checked_add(1))
            .expect("variable ID too large for DIMACS i32 representation");
        if self.is_positive() {
            var_1indexed
        } else {
            -var_1indexed
        }
    }

    /// Convert to DIMACS signed integer as `i64` (never panics).
    ///
    /// Extension variables in LRAT proofs (extended resolution) can have
    /// variable IDs up to `u32::MAX >> 1`, which exceeds `i32::MAX - 1`.
    /// This method uses `i64` arithmetic to avoid overflow on any valid
    /// literal. Prefer this in diagnostic/error paths where panicking would
    /// mask the real error (#5327).
    #[inline]
    pub fn to_dimacs_i64(self) -> i64 {
        let var_1indexed = i64::from(self.variable().id()) + 1;
        if self.is_positive() {
            var_1indexed
        } else {
            -var_1indexed
        }
    }
}

impl std::fmt::Display for Literal {
    /// Format as DIMACS signed integer. Uses `i64` internally to handle
    /// extension variables that exceed `i32::MAX` (#5327).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_dimacs_i64())
    }
}

/// Bounded model-checking harnesses that PROVE the soundness invariants of the
/// literal encoding (`positive = 2*var`, `negative = 2*var+1`) over all inputs
/// in a tractable range — the formal upgrade of the sample/dense tests in
/// `literal_tests.rs`. A wrong encoding round-trip would silently corrupt a
/// DRAT/LRAT proof checker's clause database, so these are genuine soundness
/// obligations. The harnesses are written in the `kani`-attribute format
/// (`#[cfg(kani)]` gates them out of ordinary builds) but are **executed by
/// Trust's `model-checker-consumer` bounded model checker** (which uses AY itself as its SMT
/// backend), not the standalone `kani` tool. See the
/// `[[trust-verification-toolchain]]` methodology.
#[cfg(kani)]
mod verification {
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
}

#[cfg(test)]
#[path = "literal_tests.rs"]
mod tests;
