// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the SMT backend.

use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{FarkasAnnotation, TermId};
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::BigRational;

/// Result of model verification against a CHC expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModelVerifyResult {
    /// Expression evaluates to `true` under the model.
    Valid,
    /// Expression evaluates to `false` under the model — a definite bug.
    Invalid,
    /// Expression cannot be fully evaluated (predicates, arrays, missing vars).
    /// The model may or may not satisfy the expression.
    Indeterminate,
}

/// Partition origin for a constraint in Craig interpolation.
///
/// When computing interpolants from `A ∧ B` being UNSAT, we need to know
/// which partition each conflict literal originated from. This is critical
/// for correct B-pure classification: a constraint is B-pure only if it
/// came from the B partition AND mentions only shared variables.
///
/// Reference: Z3 Spacer's `spacer_unsat_core_plugin.cpp:94-214`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Partition {
    /// Constraint came from the A partition (transition constraints).
    A,
    /// Constraint came from the B partition (bad state constraints).
    B,
    /// Constraint came from both partitions.
    #[default]
    AB,
    /// Constraint was introduced by branch-and-bound case splitting (`NeedSplit`).
    ///
    /// These atoms (e.g., `x <= floor`, `x >= ceil`) are not derived from
    /// specific A/B constraints and should be excluded from interpolation
    /// to avoid polluting the proof structure (matching Z3's treatment of
    /// DPLL hypotheses as A-side).
    ///
    /// Note: Disequality and expression splits (`NeedDisequalitySplit`,
    /// `NeedExpressionSplit`) inherit `A/B/AB` from their triggering guard
    /// atom and are NOT classified as `Split`.
    ///
    /// See the development design notes for rationale.
    Split,
}

/// UNSAT core - the subset of constraints that caused unsatisfiability
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct UnsatCoreDiagnostics {
    /// Number of DPLL(T) refinement iterations executed.
    pub dt_iterations: u64,
    /// Count of plain theory UNSAT conflicts (without Farkas certificate).
    pub theory_unsat_count: u64,
    /// Count of theory UNSAT conflicts with concrete Farkas coefficients.
    pub theory_farkas_count: u64,
    /// Count of theory UNSAT conflicts where Farkas data was missing (`None`).
    pub theory_farkas_none_count: u64,
    /// Number of theory-requested split clauses added during solving.
    pub split_count: u64,
    /// Activation assumptions from the SAT UNSAT core that map to Farkas conflicts.
    pub activation_core_conflicts: u64,
    /// Total Farkas conflicts collected before activation-core filtering.
    pub total_farkas_conflicts: u64,
}

#[derive(Debug, Clone, Default)]
pub struct UnsatCore {
    /// Conjuncts from the original query that are sufficient for UNSAT.
    ///
    /// This is currently populated only for conjunction-shaped queries where
    /// we solve under assumptions and extract an UNSAT core over those assumptions.
    pub conjuncts: Vec<ChcExpr>,

    /// Arithmetic Farkas conflicts observed while solving under assumptions.
    ///
    /// These are collected opportunistically when the arithmetic theory returns
    /// `TheoryResult::UnsatWithFarkas`. They can be used by PDR to attempt
    /// proof-based interpolation even when the background contains Boolean structure.
    pub farkas_conflicts: Vec<FarkasConflict>,

    /// Solver-level diagnostics for UNSAT-core extraction.
    ///
    /// Populated by `check_sat_with_assumption_conjuncts` when DPLL(T)-under-assumptions
    /// is used. Defaults to zeros in simpler UNSAT-core paths.
    pub diagnostics: UnsatCoreDiagnostics,
}

/// A Farkas certificate from an arithmetic theory conflict.
///
/// When LRA/LIA proves UNSAT through linear arithmetic, the Farkas lemma provides
/// non-negative coefficients such that the linear combination of constraints
/// yields a contradiction (e.g., 0 >= 1). This certificate can be used for
/// Craig interpolation in CHC solving.
#[derive(Debug, Clone)]
pub struct FarkasConflict {
    /// The conflicting constraint terms (TermIds in the SmtContext's term store).
    ///
    /// These are the theory literals that participated in the conflict. Each term
    /// is a comparison atom (e.g., `x <= 5`, `y >= 3`).
    pub conflict_terms: Vec<TermId>,

    /// Whether each conflict term was asserted positively (true) or negatively (false).
    pub polarities: Vec<bool>,

    /// Farkas coefficients for interpolation.
    ///
    /// Each coefficient corresponds to the conflict term at the same index.
    /// The coefficients are non-negative and their linear combination proves UNSAT.
    pub farkas: FarkasAnnotation,

    /// Partition origin for each conflict term (#982).
    ///
    /// Used for Craig interpolation to determine which constraints came from
    /// the A partition vs the B partition. When empty, interpolation falls back
    /// to variable-based classification.
    pub origins: Vec<Partition>,
}

/// Result of an SMT satisfiability check
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "SMT results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum SmtResult {
    /// Formula is satisfiable, with a model mapping variable names to values
    Sat(FxHashMap<String, SmtValue>),
    /// Formula is unsatisfiable, optionally with an UNSAT core
    Unsat,
    /// Formula is unsatisfiable with an UNSAT core for interpolation
    UnsatWithCore(UnsatCore),
    /// Formula is unsatisfiable with a Farkas certificate from arithmetic theory.
    ///
    /// This variant is returned when LIA/LRA directly proves UNSAT through linear
    /// arithmetic conflict. The certificate can be used for Craig interpolation.
    UnsatWithFarkas(FarkasConflict),
    /// Solver couldn't determine satisfiability
    Unknown,
}

impl SmtResult {
    /// Returns `true` if this result is any UNSAT variant (plain, with core, or with Farkas certificate).
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(
            self,
            Self::Unsat | Self::UnsatWithCore(_) | Self::UnsatWithFarkas(_)
        )
    }

    /// Returns `true` if this result is SAT (carries a model).
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    /// Returns `true` if the solver returned Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Returns a reference to the SAT model, if this result is SAT.
    #[inline]
    pub fn model(&self) -> Option<&FxHashMap<String, SmtValue>> {
        match self {
            Self::Sat(m) => Some(m),
            _ => None,
        }
    }

    /// Consumes this result and returns the SAT model, if SAT.
    #[inline]
    pub fn into_model(self) -> Option<FxHashMap<String, SmtValue>> {
        match self {
            Self::Sat(m) => Some(m),
            _ => None,
        }
    }

    /// Extracts Farkas conflicts from an UNSAT result, consuming self.
    ///
    /// Returns the clause-local Farkas certificates carried by `UnsatWithFarkas`
    /// or `UnsatWithCore` variants. Returns an empty vec for plain `Unsat`, `Sat`,
    /// and `Unknown`. Used by PDR blocking to preserve clause-local proof data
    /// for interpolation (#6484).
    #[inline]
    pub fn into_farkas_conflicts(self) -> Vec<FarkasConflict> {
        match self {
            Self::UnsatWithFarkas(conflict) => vec![conflict],
            Self::UnsatWithCore(core) => core.farkas_conflicts,
            _ => vec![],
        }
    }
}

/// A value in an SMT model
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SmtValue {
    /// Boolean value
    Bool(bool),
    /// Integer value
    ///
    /// i128-lockstep: widened from `i64` together with `ChcExpr::Int` (the
    /// evaluator converts between them). Model values beyond i128 use the
    /// [`SmtValue::BigInt`] escape variant (Phase 2).
    Int(i128),
    /// Integer value beyond `i128` range (Phase-2 BigInt escape).
    ///
    /// CANONICAL-FORM INVARIANT: this variant may only hold values that do
    /// NOT fit `i128`. Construct exclusively through
    /// [`SmtValue::int_from_bigint`] (in-range values become [`SmtValue::Int`]).
    /// Canonicality makes the derived `PartialEq` exact across the
    /// `Int`/`BigInt` split (the two domains are disjoint, so structural
    /// inequality implies semantic inequality) and keeps `smt_values_equal`'s
    /// cross-kind `Some(false)` catch-all sound. Every other consumer that
    /// matches only `Int` abstains fail-closed on this variant (never
    /// fabricates a value).
    BigInt(std::sync::Arc<num_bigint::BigInt>),
    /// Real (rational) value
    Real(BigRational),
    /// Bitvector value (value, width), with a `u128` fast path.
    BitVec(u128, u32),
    /// Exact bitvector value whose declared width exceeds 128 bits.
    ///
    /// Values enter this representation through [`SmtValue::try_bitvec_from_biguint`],
    /// which masks them to `width` bits. Keeping this separate from [`SmtValue::BitVec`]
    /// leaves the common <=128-bit evaluator path allocation-free while model
    /// extraction and validation retain every high bit of wide witnesses.
    BigBitVec(std::sync::Arc<BigUint>, u32),
    /// Opaque symbolic model value that could not be concretized.
    ///
    /// This preserves solver-generated placeholders such as `@arr33` and
    /// sort-qualified anti-unification names instead of fabricating concrete
    /// zeros that can cause false-SAT during witness verification.
    Opaque(String),
    /// Constant array: all indices map to the same default value.
    /// Represents `((as const (Array K V)) default)`.
    ConstArray(Box<Self>),
    /// Array with explicit point overrides on a default.
    /// `default` is the value for all indices not in `entries`.
    /// Each entry is `(index_value, element_value)`.
    ArrayMap {
        default: Box<Self>,
        entries: Vec<(Self, Self)>,
    },
    /// Datatype constructor application: (ctor_name, field_values).
    /// Nullary: `Datatype("Green", vec![])`.
    /// Non-nullary: `Datatype("mkpair", vec![Int(42), Bool(true)])`.
    Datatype(String, Vec<Self>),
}

impl SmtValue {
    fn validate_public_bitvec_width(width: u32) -> crate::ChcResult<()> {
        if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
            return Err(crate::ChcError::InvalidBitVectorWidth {
                width,
                max: crate::MAX_BITVECTOR_WIDTH,
            });
        }
        Ok(())
    }

    /// Build an exact bit-vector model value after validating its width.
    ///
    /// The value is reduced modulo `2^width`. This checked public entry point
    /// prevents typed clients from bypassing the parser's resource bound.
    pub fn try_bitvec_from_biguint(value: BigUint, width: u32) -> crate::ChcResult<Self> {
        Self::validate_public_bitvec_width(width)?;
        Ok(Self::bitvec_from_biguint(value, width))
    }

    /// Build a checked bit-vector model value from a `u128` payload.
    pub fn try_bitvec_from_u128(value: u128, width: u32) -> crate::ChcResult<Self> {
        Self::validate_public_bitvec_width(width)?;
        Ok(Self::bitvec_from_u128(value, width))
    }

    /// Build a checked bit-vector model value with signed modulo semantics.
    pub fn try_bitvec_from_bigint(value: BigInt, width: u32) -> crate::ChcResult<Self> {
        Self::validate_public_bitvec_width(width)?;
        Ok(Self::bitvec_from_bigint(value, width))
    }

    /// Build an integer model value from a `BigInt`, canonicalizing.
    ///
    /// This is the ONLY permitted constructor for [`SmtValue::BigInt`]
    /// (review gate: grep that `SmtValue::BigInt(` is constructed nowhere
    /// else). Values that fit `i128` become [`SmtValue::Int`]; only genuine
    /// beyond-i128 values take the `BigInt` variant, preserving the
    /// canonical-form invariant that makes derived `PartialEq` exact.
    pub(crate) fn int_from_bigint(n: num_bigint::BigInt) -> Self {
        use num_traits::ToPrimitive;
        match n.to_i128() {
            Some(small) => Self::Int(small),
            None => Self::BigInt(std::sync::Arc::new(n)),
        }
    }

    /// Build a bitvector model value from an exact unsigned integer.
    ///
    /// The value is reduced modulo `2^width`. Widths through 128 use the
    /// allocation-free [`SmtValue::BitVec`] representation; wider values use
    /// [`SmtValue::BigBitVec`] even when their numeric value happens to be small.
    pub(crate) fn bitvec_from_biguint(value: BigUint, width: u32) -> Self {
        use num_traits::{One, ToPrimitive, Zero};

        let masked = if width == 0 {
            BigUint::zero()
        } else if value.bits() <= u64::from(width) {
            // Avoid allocating a `width`-bit mask for already-normalized
            // values.  This matters for ordinary defaults such as `(_ bv0 N)`
            // when N itself is very large.
            value
        } else {
            value & ((BigUint::one() << width) - BigUint::one())
        };
        if width <= 128 {
            // Masking to at most 128 bits makes this conversion infallible.
            let Some(small) = masked.to_u128() else {
                unreachable!("a value masked to 128 bits must fit u128");
            };
            Self::BitVec(small, width)
        } else {
            Self::BigBitVec(std::sync::Arc::new(masked), width)
        }
    }

    /// Build a bitvector model value from a `u128`, canonicalizing its width.
    ///
    /// This is the allocation-free constructor for the common <=128-bit path.
    /// A `u128` is already in range for every wider sort, so widths above 128
    /// only allocate the exact backing integer and never need a mask.
    pub(crate) fn bitvec_from_u128(value: u128, width: u32) -> Self {
        if width <= 128 {
            let masked = match width {
                0 => 0,
                128 => value,
                _ => value & ((1u128 << width) - 1),
            };
            Self::BitVec(masked, width)
        } else {
            Self::BigBitVec(std::sync::Arc::new(BigUint::from(value)), width)
        }
    }

    /// Build a bitvector model value from a signed integer using SMT-LIB's
    /// modulo-`2^width` `int_to_bv` semantics.
    pub(crate) fn bitvec_from_bigint(value: BigInt, width: u32) -> Self {
        use num_traits::{One, Signed};

        if width == 0 {
            return Self::bitvec_from_u128(0, 0);
        }
        if !value.is_negative() {
            let Some(unsigned) = value.to_biguint() else {
                unreachable!("a non-negative BigInt must convert to BigUint");
            };
            return Self::bitvec_from_biguint(unsigned, width);
        }

        let modulus = BigInt::from_biguint(Sign::Plus, BigUint::one() << width);
        let mut reduced = value % &modulus;
        if reduced.is_negative() {
            reduced += modulus;
        }
        let Some(unsigned) = reduced.to_biguint() else {
            unreachable!("a reduced bitvector residue must be non-negative");
        };
        Self::bitvec_from_biguint(unsigned, width)
    }

    /// Return an exact unsigned bitvector value and its declared width.
    ///
    /// Direct legacy `BitVec` construction is normalized here as well, so an
    /// over-wide `u128` payload at a narrow width cannot leak non-bitvector bits
    /// into exact evaluator operations. Returns `None` for a non-BV value or a
    /// width outside `1..=`[`crate::MAX_BITVECTOR_WIDTH`], including malformed
    /// enum variants constructed directly by downstream code.
    pub fn bitvec_to_biguint(&self) -> Option<(BigUint, u32)> {
        match self {
            Self::BitVec(value, width) => {
                if *width == 0 || *width > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                let normalized = Self::bitvec_from_u128(*value, *width);
                match normalized {
                    Self::BitVec(value, width) => Some((BigUint::from(value), width)),
                    Self::BigBitVec(value, width) => Some((value.as_ref().clone(), width)),
                    _ => unreachable!("bitvec constructor returned a non-bitvector value"),
                }
            }
            Self::BigBitVec(value, width) => {
                // Check the public resource bound before normalization. A
                // directly-constructed non-canonical enum variant may carry
                // `u32::MAX`; building its modulo mask first would itself be
                // an attacker-controlled allocation.
                if *width == 0 || *width > crate::MAX_BITVECTOR_WIDTH {
                    return None;
                }
                let normalized = Self::bitvec_from_biguint(value.as_ref().clone(), *width);
                match normalized {
                    Self::BitVec(value, width) => Some((BigUint::from(value), width)),
                    Self::BigBitVec(value, width) => Some((value.as_ref().clone(), width)),
                    _ => unreachable!("bitvec constructor returned a non-bitvector value"),
                }
            }
            _ => None,
        }
    }

    /// Convert a concrete bitvector model value into an exact CHC literal.
    ///
    /// Wide literals are represented as a high-to-low `concat` tree of
    /// allocation-free, at-most-128-bit [`ChcExpr::BitVec`] leaves, matching
    /// the parser's representation for wide SMT-LIB literals.
    /// Returns `None` for a non-bit-vector value or a declared width outside
    /// `1..=`[`crate::MAX_BITVECTOR_WIDTH`]. The latter check keeps public
    /// replay/rendering code fail-closed even if it receives a directly-built,
    /// non-canonical [`SmtValue`] variant.
    pub fn bitvec_to_chc_expr(&self) -> Option<ChcExpr> {
        use num_traits::{One, ToPrimitive};

        let (mut value, width) = self.bitvec_to_biguint()?;
        if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
            return None;
        }
        if width <= 128 {
            return value.to_u128().map(|value| ChcExpr::BitVec(value, width));
        }

        let mut chunks = Vec::new();
        let mut bits_left = width;
        while bits_left != 0 {
            let chunk_width = bits_left.min(128);
            let mask = (BigUint::one() << chunk_width) - BigUint::one();
            let chunk = (&value & mask).to_u128()?;
            chunks.push((chunk, chunk_width));
            value >>= chunk_width;
            bits_left -= chunk_width;
        }

        let (low, low_width) = *chunks.first()?;
        let mut result = ChcExpr::BitVec(low, low_width);
        for &(chunk, chunk_width) in chunks.iter().skip(1) {
            result = ChcExpr::Op(
                ChcOp::BvConcat,
                vec![
                    std::sync::Arc::new(ChcExpr::BitVec(chunk, chunk_width)),
                    std::sync::Arc::new(result),
                ],
            );
        }
        Some(result)
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum DiseqGuardKind {
    Distinct,
    Eq,
}
