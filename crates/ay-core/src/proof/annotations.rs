// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Payload annotations attached to theory-lemma proof steps.

use crate::term::TermId;
use num_rational::Rational64;
use serde::{Deserialize, Serialize};

/// Capacity-hint clamp for clause-length-sized scratch vectors; clause length
/// is producer-controlled, and longer clauses just grow past the hint.
const MAX_PREALLOC_CLAUSE_LITERALS: usize = 1 << 16;

/// Farkas annotation for arithmetic theory lemmas
///
/// When an arithmetic theory (LRA/LIA) produces an UNSAT conflict, the
/// Farkas lemma provides coefficients λ₁, λ₂, ..., λₙ ≥ 0 such that
/// combining the constraints Σλᵢcᵢ produces a contradiction (0 ≤ negative).
///
/// These coefficients are essential for Craig interpolation: the interpolant
/// is computed by combining only the A-partition constraints weighted by
/// their Farkas coefficients.
///
/// # Example
///
/// For constraints:
/// ```text
/// x ≤ 5    (from A)
/// x ≥ 10   (from B)
/// ```
///
/// Farkas coefficients λ₁ = λ₂ = 1 give:
/// ```text
/// 1·(x ≤ 5) + 1·(-x ≤ -10) → (0 ≤ -5)  contradiction
/// ```
///
/// The interpolant (from A only): `x ≤ 5`
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FarkasAnnotation {
    /// Farkas coefficients for each constraint in the conflict
    /// Indexed by position in the clause (same order as `clause` field)
    ///
    /// `Rational64 = Ratio<i64>` loses its own `Serialize`/`Deserialize` when
    /// the `num-rational/serde` feature is off, so the codec is supplied
    /// locally. It does NOT widen what this struct accepts —
    /// `deny_unknown_fields` above is untouched.
    #[serde(with = "crate::serde_bignum::rational64_vec")]
    pub coefficients: Vec<Rational64>,
}

impl FarkasAnnotation {
    /// Create a new Farkas annotation with the given coefficients
    #[must_use]
    pub fn new(coefficients: Vec<Rational64>) -> Self {
        Self { coefficients }
    }

    /// Create from integer coefficients (convenience method)
    #[must_use]
    pub fn from_ints(coefficients: &[i64]) -> Self {
        Self {
            coefficients: coefficients.iter().map(|&c| Rational64::from(c)).collect(),
        }
    }

    /// Check if all coefficients are non-negative (valid Farkas certificate)
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.coefficients.iter().all(|c| *c >= Rational64::from(0))
    }

    /// Rebind position-indexed coefficients from `source_clause` to
    /// `target_clause` by literal identity.
    ///
    /// SAT watched-literal movement and clause normalization may permute or
    /// deduplicate a clause without changing it. Coefficients for duplicate
    /// source literals are summed; the sum is placed on the first target
    /// occurrence and later duplicates receive zero. A source literal may be
    /// dropped only when its merged coefficient is zero. Target-only literals
    /// are sound weakening rows and receive zero. A duplicate-literal merge
    /// whose sum overflows `Rational64` declines. Any other mismatch declines.
    #[must_use]
    pub fn rebind_by_literal(
        &self,
        source_clause: &[TermId],
        target_clause: &[TermId],
    ) -> Option<Self> {
        use num_traits::CheckedAdd;
        use std::collections::{BTreeMap, BTreeSet};

        if self.coefficients.len() != source_clause.len() {
            return None;
        }
        if source_clause == target_clause {
            return Some(self.clone());
        }

        let zero = Rational64::from(0);
        let mut by_literal: BTreeMap<TermId, Rational64> = BTreeMap::new();
        for (&literal, coefficient) in source_clause.iter().zip(self.coefficients.iter()) {
            let merged = by_literal.entry(literal).or_insert(zero);
            *merged = merged.checked_add(coefficient)?;
        }

        let mut seen = BTreeSet::new();
        let mut rebound = Vec::with_capacity(target_clause.len().min(MAX_PREALLOC_CLAUSE_LITERALS));
        for &literal in target_clause {
            if seen.insert(literal) {
                rebound.push(by_literal.remove(&literal).unwrap_or(zero));
            } else {
                rebound.push(zero);
            }
        }
        if by_literal.values().any(|coefficient| *coefficient != zero) {
            return None;
        }
        Some(Self::new(rebound))
    }
}

/// LIA-specific proof annotation for integer arithmetic theory lemmas.
///
/// LIA conflicts can arise from three distinct proof shapes:
/// - **BoundsGap**: effective lower bound > upper bound (e.g., x >= 6 AND x <= 5)
/// - **Divisibility**: GCD test fails (e.g., 2|x AND x = 3)
/// - **CuttingPlane**: Farkas combination followed by integer rounding (Gomory cut)
///
/// When present on a `TheoryLemma` or `TheoryLemmaProof`, this annotation tells
/// the strict-mode proof checker which LIA-specific validation to apply.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum LiaAnnotation {
    /// Bounds gap: the effective integer bounds are contradictory.
    ///
    /// A Farkas-style combination of the conflict literals produces
    /// `lower > upper` when rounded to integers.
    BoundsGap,

    /// Divisibility conflict: GCD of constraint coefficients does not divide
    /// the constant, proving no integer solution exists.
    Divisibility,

    /// Cutting plane: a Farkas combination followed by integer rounding
    /// (division + ceiling) produces a contradiction.
    CuttingPlane(CuttingPlaneAnnotation),

    /// Linear identity: a POSITIVE equality `(= L R)` whose difference `L - R`
    /// reduces to the identically-zero integer linear form (every variable
    /// coefficient 0 and the constant 0), so `L = R` holds for ALL integer
    /// assignments. Validates the tautology direction (e.g. `(* x 0) = 0`,
    /// `(* x 1) = x`), as opposed to the infeasibility annotations above.
    LinearIdentity,
}

/// Annotation for a cutting-plane (Gomory cut) proof step.
///
/// The cutting plane derivation:
/// 1. Combine conflict literals using Farkas coefficients (same as LRA)
/// 2. Divide all coefficients by `divisor`
/// 3. Round up (ceiling) to obtain tighter integer bounds
/// 4. The tightened bound contradicts existing constraints
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CuttingPlaneAnnotation {
    /// Farkas coefficients for the linear combination step
    pub farkas: FarkasAnnotation,
    /// Divisor for the cutting-plane rounding step (must be > 0)
    pub divisor: i64,
}

/// Type of BV gate for bit-blast proof annotation.
///
/// Each variant corresponds to an SMT-LIB bitvector operation that the
/// bit-blaster encodes into propositional clauses. Carrying the gate type
/// in the proof allows the checker and printer to emit `bv_bitblast`
/// instead of the unverified `trust` fallback.
///
/// Reference: CVC5 `src/theory/bv/bitblast/proof_bitblaster.cpp`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BvGateType {
    /// Bitwise AND (`bvand`)
    And,
    /// Bitwise OR (`bvor`)
    Or,
    /// Bitwise XOR (`bvxor`)
    Xor,
    /// Bitwise NOT (`bvnot`)
    Not,
    /// Addition (`bvadd`)
    Add,
    /// Multiplication (`bvmul`)
    Mul,
    /// Negation (`bvneg`)
    Neg,
    /// Shift left (`bvshl`)
    Shl,
    /// Logical shift right (`bvlshr`)
    Lshr,
    /// Arithmetic shift right (`bvashr`)
    Ashr,
    /// Equality (`=` on bitvectors)
    Eq,
    /// Unsigned less-than (`bvult`)
    Ult,
    /// Concatenation (`concat`)
    Concat,
    /// Extraction (`extract`)
    Extract,
    /// Zero extension (`zero_extend`)
    ZeroExtend,
    /// Sign extension (`sign_extend`)
    SignExtend,
    /// Unsigned division (`bvudiv`)
    Udiv,
    /// Unsigned remainder (`bvurem`)
    Urem,
    /// Constant bit-vector literal
    Const,
    /// Variable (bit-blast a BV variable into Boolean bits)
    Variable,
    /// MUX / if-then-else on bitvectors
    Ite,
}

impl std::fmt::Display for BvGateType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::And => "bvand",
            Self::Or => "bvor",
            Self::Xor => "bvxor",
            Self::Not => "bvnot",
            Self::Add => "bvadd",
            Self::Mul => "bvmul",
            Self::Neg => "bvneg",
            Self::Shl => "bvshl",
            Self::Lshr => "bvlshr",
            Self::Ashr => "bvashr",
            Self::Eq => "=",
            Self::Ult => "bvult",
            Self::Concat => "concat",
            Self::Extract => "extract",
            Self::ZeroExtend => "zero_extend",
            Self::SignExtend => "sign_extend",
            Self::Udiv => "bvudiv",
            Self::Urem => "bvurem",
            Self::Const => "const",
            Self::Variable => "variable",
            Self::Ite => "ite",
        };
        f.write_str(s)
    }
}
