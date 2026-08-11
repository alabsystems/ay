// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof representation for AY
//!
//! Proofs can be produced for unsatisfiable formulas.
//! Supports export to Alethe format for independent verification.
//!
//! ## Alethe Proof Format
//!
//! The Alethe format (used by carcara proof checker) has three main commands:
//! - `assume`: Input assertions from the problem
//! - `step`: Proof steps with a rule name, premises, and conclusion clause
//! - `anchor`: Subproofs (for nested reasoning)
//!
//! Example Alethe proof:
//! ```text
//! (assume h1 (= a b))
//! (assume h2 (= b c))
//! (step t1 (cl (= a c)) :rule trans :premises (h1 h2))
//! (step t2 (cl (not (= a c)) (= a c)) :rule equiv_pos1 :premises (t1))
//! ```

use crate::term::TermId;
use num_rational::Rational64;
use serde::{Deserialize, Serialize};

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
pub struct FarkasAnnotation {
    /// Farkas coefficients for each constraint in the conflict
    /// Indexed by position in the clause (same order as `clause` field)
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
    /// are sound weakening rows and receive zero. Any other mismatch declines.
    #[must_use]
    pub fn rebind_by_literal(
        &self,
        source_clause: &[TermId],
        target_clause: &[TermId],
    ) -> Option<Self> {
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
            *by_literal.entry(literal).or_insert(zero) += *coefficient;
        }

        let mut seen = BTreeSet::new();
        let mut rebound = Vec::with_capacity(target_clause.len());
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
pub struct CuttingPlaneAnnotation {
    /// Farkas coefficients for the linear combination step
    pub farkas: FarkasAnnotation,
    /// Divisor for the cutting-plane rounding step (must be > 0)
    pub divisor: i64,
}

/// IEEE 754 floating-point operation for FP→BV proof annotation.
///
/// Each variant corresponds to an SMT-LIB floating-point operation that the
/// FP solver lowers to bitvector circuits. Carrying the operation type in the
/// proof allows the checker and printer to emit `fp_to_bv` instead of the
/// unverified `trust` fallback.
///
/// Reference: SMT-LIB FloatingPoint theory definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum FpOp {
    /// Floating-point addition (`fp.add`)
    Add,
    /// Floating-point subtraction (`fp.sub`)
    Sub,
    /// Floating-point multiplication (`fp.mul`)
    Mul,
    /// Floating-point division (`fp.div`)
    Div,
    /// Floating-point square root (`fp.sqrt`)
    Sqrt,
    /// Floating-point negation (`fp.neg`)
    Neg,
    /// Floating-point absolute value (`fp.abs`)
    Abs,
    /// Fused multiply-add (`fp.fma`)
    Fma,
    /// IEEE 754 equality (`fp.eq`)
    Eq,
    /// Floating-point less-than (`fp.lt`)
    Lt,
    /// Floating-point less-or-equal (`fp.leq`)
    Le,
    /// Floating-point greater-than (`fp.gt`)
    Gt,
    /// Floating-point greater-or-equal (`fp.geq`)
    Ge,
    /// Convert to real (`fp.to_real`)
    ToReal,
    /// Convert from real (to_fp from Real)
    FromReal,
    /// Convert to signed bitvector (`fp.to_sbv`)
    ToSbv,
    /// Convert to unsigned bitvector (`fp.to_ubv`)
    ToUbv,
    /// Convert from signed bitvector (to_fp from signed BV)
    FromSbv,
    /// Convert from unsigned bitvector (`to_fp_unsigned`)
    FromUbv,
    /// Round to integral (`fp.roundToIntegral`)
    RoundToIntegral,
    /// Floating-point minimum (`fp.min`)
    Min,
    /// Floating-point maximum (`fp.max`)
    Max,
    /// Floating-point remainder (`fp.rem`)
    Rem,
    /// Classification: isNaN (`fp.isNaN`)
    IsNaN,
    /// Classification: isInfinite (`fp.isInfinite`)
    IsInfinite,
    /// Classification: isZero (`fp.isZero`)
    IsZero,
    /// Classification: isNormal (`fp.isNormal`)
    IsNormal,
    /// Classification: isSubnormal (`fp.isSubnormal`)
    IsSubnormal,
    /// Classification: isPositive (`fp.isPositive`)
    IsPositive,
    /// Classification: isNegative (`fp.isNegative`)
    IsNegative,
    /// SMT-LIB structural equality on FP sort (`=` on FloatingPoint)
    StructuralEq,
    /// Convert to IEEE BV representation (`fp.to_ieee_bv`)
    ToIeeeBv,
    /// Convert from FP to FP (to_fp from FloatingPoint)
    FromFp,
}

impl std::fmt::Display for FpOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Add => "fp.add",
            Self::Sub => "fp.sub",
            Self::Mul => "fp.mul",
            Self::Div => "fp.div",
            Self::Sqrt => "fp.sqrt",
            Self::Neg => "fp.neg",
            Self::Abs => "fp.abs",
            Self::Fma => "fp.fma",
            Self::Eq => "fp.eq",
            Self::Lt => "fp.lt",
            Self::Le => "fp.leq",
            Self::Gt => "fp.gt",
            Self::Ge => "fp.geq",
            Self::ToReal => "fp.to_real",
            Self::FromReal => "to_fp_real",
            Self::ToSbv => "fp.to_sbv",
            Self::ToUbv => "fp.to_ubv",
            Self::FromSbv => "to_fp_sbv",
            Self::FromUbv => "to_fp_unsigned",
            Self::RoundToIntegral => "fp.roundToIntegral",
            Self::Min => "fp.min",
            Self::Max => "fp.max",
            Self::Rem => "fp.rem",
            Self::IsNaN => "fp.isNaN",
            Self::IsInfinite => "fp.isInfinite",
            Self::IsZero => "fp.isZero",
            Self::IsNormal => "fp.isNormal",
            Self::IsSubnormal => "fp.isSubnormal",
            Self::IsPositive => "fp.isPositive",
            Self::IsNegative => "fp.isNegative",
            Self::StructuralEq => "fp_structural_eq",
            Self::ToIeeeBv => "fp.to_ieee_bv",
            Self::FromFp => "to_fp_fp",
        };
        f.write_str(s)
    }
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

/// Kind of theory lemma for proof export
///
/// Different theory conflict types map to different Alethe proof rules.
/// This enum specifies which rule to use when exporting the proof.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
#[non_exhaustive]
pub enum TheoryLemmaKind {
    /// EUF transitivity chain: `(cl (not (= a b)) (not (= b c)) ... (= a z))`
    /// Uses Alethe rule `eq_transitive`
    EufTransitive,

    /// EUF reflexivity: `(cl (= a a))`. Uses Alethe rule `eq_reflexive`.
    ///
    /// The degenerate case of a transitivity conflict: when a refuted
    /// disequality's two sides are the SAME term, the connecting chain is
    /// empty and there is no transitivity to state. Emitting that as
    /// [`Self::EufTransitive`] produced a ONE-literal `eq_transitive` clause,
    /// which the strict checker rejects outright ("EufTransitive clause must
    /// have at least 2 literals") — so the refutation was correct but
    /// uncertifiable, and mandatory certification degraded it to `unknown`.
    /// Reflexivity is a rule in its own right and its clause is legitimately a
    /// unit, so the conflict is stated as what it actually is.
    EufReflexive,

    /// EUF congruence: `(cl (not (= a x)) ... (= (f a) (f x)))`
    /// Uses Alethe rule `eq_congruent`
    EufCongruent,

    /// EUF congruence on predicates: `(cl (not (= a x)) ... (not (p a)) (p x))`
    /// Uses Alethe rule `eq_congruent_pred`
    EufCongruentPred,

    /// LRA Farkas lemma: linear combination yields contradiction
    /// Uses Alethe rule `la_generic`
    LraFarkas,

    /// LIA: may include cutting planes or GCD reasoning
    /// Uses Alethe rule `lia_generic`
    LiaGeneric,

    /// Euclidean integer-remainder range theorem.
    ///
    /// The clause is exactly `(cl (not (= (mod x d) r)))` (equality
    /// orientation may be swapped), where `d` and `r` are integer constants,
    /// `d != 0`, and `r` lies outside `0 <= r < |d|`.  AY's strict checker
    /// independently validates the complete schema; a variable/zero divisor,
    /// an in-range remainder, or any other shape is rejected fail-closed.
    ///
    /// Alethe has no general symbolic `mod`-range rule, so this internal
    /// certificate renders as an honest `hole` on that wire rather than being
    /// mislabeled as `lia_generic`.
    LiaModRange,

    /// Bitvector bit-blasting (legacy, no gate info).
    /// Uses Alethe rule `bv_bitblast`.
    BvBitBlast,

    /// Bitvector bit-blasting with gate type annotation.
    /// Uses Alethe rule `bv_bitblast`.
    /// Carries the specific gate type and operand width for proof checking.
    BvBitBlastGate {
        /// The BV operation that was bit-blasted.
        gate_type: BvGateType,
        /// Bit-width of the operation's operands.
        width: u32,
    },

    /// Array read-over-write (select-store) axiom.
    ///
    /// When `index_eq` is true (positive case):
    ///   `(= (select (store a i v) i) v)`
    /// When `index_eq` is false (negative case):
    ///   `(=> (not (= i j)) (= (select (store a i v) j) (select a j)))`
    ///
    /// Uses Alethe rules `read_over_write_pos` / `read_over_write_neg`.
    ArraySelectStore {
        /// True if indices are equal (positive case), false if not equal (negative case).
        index_eq: bool,
    },

    /// Array store-permutation axiom (store-commutativity, n-ary).
    ///
    /// Two `store` chains over the SAME base array that write the SAME
    /// multiset of `(index, value)` pairs denote the same array, provided the
    /// indices are pairwise distinct. The clause therefore carries the
    /// disjointness side condition explicitly, one literal per unordered pair:
    ///
    /// ```text
    /// (cl (= i_1 i_2) … (= i_{n-1} i_n)
    ///     (= (store … (store b i_1 v_1) … i_n v_n)
    ///        (store … (store b i_{σ1} v_{σ1}) … i_{σn} v_{σn})))
    /// ```
    ///
    /// Uses Alethe rule `store_permutation`. Validated by `ay-proof`
    /// `validate_array_store_permutation` (exact schema; fail-closed).
    ArrayStorePermutation,

    /// Array read-over-write evaluated through a `store` CHAIN, optionally
    /// under an array equality premise (the n-ary generalization of
    /// `ArraySelectStore`).
    ///
    /// Chain evaluation, no premise:
    /// ```text
    /// (cl (= x i_1) … (= x i_k) (= (select C x) eval(C, x)))
    /// ```
    /// Under an array equality:
    /// ```text
    /// (cl (not (= L R)) (= x i_1) … (= x i_k) (= eval(L, x) eval(R, x)))
    /// ```
    /// where `eval(C, x)` walks `C`'s store chain outermost-first, taking the
    /// value of the first entry whose index is syntactically `x`, and skipping
    /// an entry only when the clause carries the matching `(= x i)` literal.
    ///
    /// Uses Alethe rule `read_over_write_chain`. Validated by `ay-proof`
    /// `validate_array_row_chain` (exact schema; fail-closed).
    ArrayRowChain,

    /// Folded congruence for the model-default operator on a constant array.
    ///
    /// ```text
    /// (cl (not (= A (store* ((as const (Array I E)) v))))
    ///     (= (default A) v))
    /// ```
    ///
    /// `store*` is a bounded, cycle-free chain of exactly well-sorted stores.
    /// Equality and clause orientations may be swapped, but the array, fill,
    /// and sorts must match exactly. AY's strict checker independently
    /// validates this schema. The pinned external Alethe checker has no rule
    /// for the non-standard `default` operator, so Alethe export refuses this
    /// internal certificate instead of emitting `trust` or a false rule name.
    ArrayDefaultConst,

    /// Set cardinality is non-negative: `(<= 0 (set.card s))` for any set `s`.
    ///
    /// Universally valid for every set term, with no side conditions -- a set
    /// has a non-negative number of elements whatever it contains. AY injects
    /// this bridge axiom for every `set.card` term it sees, and because the
    /// axiom is solver-generated rather than authored it cannot stay an
    /// `Assume` in the refutation; without a kind of its own it was rewritten
    /// to `hole`, which made every `set.card` refutation externally uncheckable
    /// even though the rest of the proof checked.
    ///
    /// AY's strict checker validates the schema itself. Like
    /// [`Self::ArrayDefaultConst`], the pinned external Alethe checker has no
    /// rule for the non-standard `set.card` operator, so Alethe export refuses
    /// this internal certificate rather than emitting a false rule name.
    SetCardNonNegative,

    /// Set cardinality membership lower bound:
    /// `(ite (member x s) (<= 1 (set.card s)) (<= 0 (set.card s)))`.
    ///
    /// Universally valid: a set with a known member has at least one element,
    /// and the else branch is the unconditional non-negativity bound. The set
    /// under the membership test and the set under the cardinality must be the
    /// SAME term -- that identity is the whole content of the axiom, and
    /// dropping it would licence `x ∈ s => |t| >= 1` for an unrelated `t`.
    ///
    /// Like [`Self::SetCardNonNegative`], checkable only by AY's native strict
    /// checker; the pinned external Alethe checker has no `set.card` rule.
    SetCardMemberLowerBound,

    /// The empty set has cardinality zero: `(= (set.card e) 0)` where `e` is
    /// SYNTACTICALLY empty -- a `set.empty` application, or the constant array
    /// whose fill is `false`.
    ///
    /// The fill must be exactly `false`. A `true` fill is the UNIVERSAL set,
    /// whose cardinality is the index sort's size (infinite over `Int`), so a
    /// schema that ignored the fill would licence `|universe| = 0` and let a
    /// refutation be built out of nothing.
    ///
    /// Only the syntactic form is covered. A set that is empty only by virtue
    /// of an assertion (`(= s (as set.empty ...))`) is NOT licensed here --
    /// that needs problem context this checker does not receive.
    SetCardEmpty,

    /// Cardinality lower bound from a counted membership tree:
    ///
    /// ```text
    /// (ite (member i1 s) (ite (member i2 s) (<= 2 (set.card s)) (<= 1 ...))
    ///                    (ite (member i2 s) (<= 1 (set.card s)) (<= 0 ...)))
    /// ```
    ///
    /// Each leaf bounds the cardinality below by the number of memberships
    /// that hold on the path to it, which is valid because a set containing
    /// `k` DISTINCT elements has at least `k` of them.
    ///
    /// Distinctness is the load-bearing side condition, and it is why the
    /// schema requires every index to be an integer LITERAL with pairwise
    /// distinct values: two variable indices could denote the same element, so
    /// counting them separately would licence `|{x}| >= 2`.
    SetCardMemberCount,

    /// `(= (set.card s) 0)` where the PROBLEM asserts `s` empty.
    ///
    /// Unlike [`Self::SetCardEmpty`] this is NOT a tautology: the set is empty
    /// only by virtue of an assertion, so the schema alone cannot license it.
    /// Accepted against a registry built from the problem's TOP-LEVEL asserted
    /// equalities, closed to a fixpoint -- the same shape of whole-proof
    /// provenance [`Self::ArrayExtensionality`] uses. No problem assertions
    /// means no evidence, and the lemma fails closed.
    SetCardEmptyByAssertion,

    /// Array extensionality axiom.
    ///
    /// `(=> (forall ((i Index)) (= (select a i) (select b i))) (= a b))`
    ///
    /// Uses Alethe rule `extensionality`.
    ArrayExtensionality,

    /// Floating-point to bitvector translation (IEEE 754 encoding faithfulness).
    /// Uses Alethe rule `fp_to_bv`.
    /// Composes with `BvBitBlast`/`BvBitBlastGate`: the FP operation is first
    /// lowered to a BV circuit, then that circuit is bit-blasted to SAT.
    FpToBv {
        /// The FP operation that was lowered to bitvector circuits.
        operation: FpOp,
    },

    /// String length axiom: `len(concat(a, b)) = len(a) + len(b)`, `len("") = 0`,
    /// `len(a) >= 0`, etc.
    ///
    /// Uses Alethe rule `string_length`.
    StringLengthAxiom,

    /// Universally-valid `str.len` theorem over SYMBOLIC subjects — the certified
    /// counterpart of the solver's injected length axioms
    /// (`collect_str_len_axioms_from_roots`). The clause carries a literal that
    /// is one of: the concat-length sum
    /// `(= (str.len (str.++ a…)) (+ (str.len a)…))`, the empty↔zero-length
    /// biconditional `(or ±(= x "") ∓(= (str.len x) 0))`, non-negativity
    /// `(<= 0 (str.len x))`, the constant length `(= k (str.len c))`, the
    /// equal-length congruence `(or (not (= s t)) (= (str.len s) (str.len t)))`,
    /// or a containment/prefix/suffix length bound
    /// `(or (not (str.contains x s)) (<= (str.len s) (str.len x)))`. Each holds
    /// under EVERY interpretation, so the unit clause introducing it is a valid
    /// theory lemma.
    ///
    /// Uses Alethe rule `string_length_lemma`; validated by `ay-proof` with an
    /// INDEPENDENT structural checker that re-derives the exact algebraic
    /// identity (multiset-matched concat operands, opposite-polarity `or`,
    /// exact bound/constant), fail-closed on any near-miss. This lets the
    /// injected length facts carry a certified rule instead of surfacing as
    /// foreign `assume` leaves the #8821 provenance gate rejects (#selfcert-strlen).
    StringLengthLemma,

    /// String content axiom: substr, contains, replace, indexof rewriting.
    ///
    /// Uses Alethe rule `string_decompose`.
    StringContentAxiom,

    /// String normal form decomposition: word equation normal form reasoning,
    /// `str.to_code` / `str.from_code` injectivity.
    ///
    /// Uses Alethe rule `string_code_inj`.
    StringNormalForm,

    /// Ground string/regex evaluation: the clause carries a literal every one
    /// of whose leaves is a constant (or a regular expression built only from
    /// constants) and which evaluates to TRUE under the SMT-LIB Unicode-string
    /// semantics — e.g. `(not (str.in_re "/mod/forum/" (re.++ .. )))`. A clause
    /// with a literal true under every interpretation is a tautology.
    ///
    /// Uses Alethe rule `string_ground_eval`; validated by `ay-proof` with an
    /// INDEPENDENT ground evaluator (a memoized interval regex matcher, not the
    /// solver's `WeRegex`/`RegexSolver` code), fail-closed on any non-ground
    /// leaf, unimplemented operator, or budget exhaustion.
    StringGroundEval,

    /// Regex intersection-emptiness over a SYMBOLIC string term: the clause
    /// carries a group of literals `±(str.in_re t Rᵢ)` over one common term `t`
    /// whose regexes are all ground, and the intersection of the languages the
    /// group DENIES is empty — e.g.
    /// `(cl (not (str.in_re X R₁)) (not (str.in_re X R₂)))` where
    /// `L(R₁) ∩ L(R₂) = ∅`. No `t` falsifies the whole group, so some literal
    /// is true under every interpretation and the clause is a tautology.
    /// A negated membership contributes the exact complement `¬L(R)`.
    ///
    /// This is the SYMBOLIC counterpart of [`Self::StringGroundEval`], which
    /// only decides facts whose subject is a constant.
    ///
    /// Uses Alethe rule `regex_intersect_empty`; validated by `ay-proof` with
    /// an INDEPENDENT derivative-product emptiness checker (a hash-consed
    /// arena over code-point interval sets with a verified total partition of
    /// the SMT-LIB alphabet — not the solver's `WeRegex` search), fail-closed
    /// on any non-ground leaf, unimplemented operator, incomplete alphabet
    /// partition, reachable accepting state, or budget exhaustion.
    RegexIntersectEmpty,

    /// Datatype constructor distinctness: `(cl (not (= t C1)) (not (= t C2)))`
    /// where `C1` and `C2` are applications of DISTINCT constructors of the same
    /// datatype — a value cannot equal two different constructors. Uses Alethe
    /// rule `dt_distinct`; validated by `ay-proof` against the datatype
    /// constructor registry (the proof-checker must be given the datatype
    /// declarations; without them this kind fails closed in strict mode).
    DatatypeDistinct,

    /// Datatype selector projection: `(cl (= (sel_i (C a_0 .. a_n)) a_i))` where
    /// `sel_i` is the field-`i` selector of constructor `C` — reading the `i`-th
    /// field of a constructor application yields its `i`-th argument. Uses Alethe
    /// rule `dt_project`; validated by `ay-proof` against the constructor→selector
    /// registry (the proof checker must be given the selector declarations;
    /// without them this kind fails closed in strict mode).
    DatatypeSelectorProject,

    /// Datatype tester evaluation on a constructor application. The positive
    /// unit `(cl (is-C (C a_0 .. a_n)))` is valid for the matching
    /// constructor, while `(cl (not (is-C (D ...))))` is valid when `C` and
    /// `D` are distinct constructors of the same datatype. Uses AY's
    /// `dt_tester` rule and is validated by `ay-proof` against the datatype
    /// constructor registry; without that registry strict mode fails closed.
    DatatypeTesterEval,

    /// Bounded exact tautology over a pure total-order / term-ITE fragment.
    /// Numeric leaves are at most six Int or Real variables; numeric terms may
    /// only select such leaves through `ite`, and Boolean structure may only
    /// compare them or combine comparisons propositionally. Truth therefore
    /// depends solely on the variables' finite total preorder. `ay-proof`
    /// enumerates every preorder representative and rejects constants,
    /// arithmetic, UFs, unsupported Boolean atoms, or an oversized formula.
    OrderIteTautology,

    /// Boolean tautology: a propositional/Boolean clause TRUE under every
    /// assignment of its bounded variables (e.g. `(= (not (not p)) p)`,
    /// `(= (and p p) p)`). Uses Alethe rule `bool_tautology`; validated by
    /// `ay-proof` via exhaustive bounded evaluation over the Bool/small-BV
    /// variables.
    BoolTautology,

    /// If-then-else with identical branches: `(= (ite c x x) x)` — a conditional
    /// whose two branches are the same term equals that branch, for ANY condition
    /// `c` and ANY sort of `x`. Uses Alethe rule `ite_same`; validated
    /// syntactically by `ay-proof` (the two `ite` branches are the same `TermId`,
    /// and equal to the other side of the equality).
    IteSame,

    /// Floating-point classification / sign / structural-equality / comparison
    /// identity: a propositional clause over `fp.is*`, `fp.abs`, `fp.neg`, `=`
    /// (structural FP), `fp.eq`, and `fp.lt`/`leq`/`gt`/`geq` that is TRUE under
    /// every assignment of its small-width FP variables (e.g.
    /// `(= (fp.abs (fp.abs x)) (fp.abs x))`, `(= (fp.neg (fp.neg x)) x)`,
    /// `(not (and (fp.isNaN x) (fp.isNormal x)))`). Uses Alethe rule
    /// `fp_classification`; validated by `ay-proof` via exhaustive bounded
    /// evaluation with a self-contained EXACT (integer/rational) IEEE-754
    /// evaluator. FP ARITHMETIC ops are out of scope and fail closed.
    FpClassification {
        /// The principal FP operation the lemma is about (carried for rendering
        /// and diagnostics; validation re-derives soundness from the clause).
        operation: FpOp,
    },

    /// IEEE-754 rounding-mode finite-domain axiom.
    ///
    /// `RoundingMode` has exactly the five SMT-LIB values `RNE`, `RNA`, `RTP`,
    /// `RTN`, and `RTZ`, even though AY's core term representation uses an
    /// uninterpreted sort. This kind certifies the exact pairwise distinctness
    /// conjunction for those five constants, one of its exact disequality
    /// leaves after top-level conjunction flattening, the exact coverage
    /// disjunction saying that a rounding-mode term equals one of them, or the
    /// complete six-term pigeonhole theorem for that five-value domain. Clauses
    /// may contain additional weakening literals once one exact theorem is
    /// present.
    ///
    /// Uses Alethe rule `fp_rm_domain`; strict validation independently checks
    /// the closed schemas and rejects every partial/extra variant.
    FpRoundingModeDomain,

    /// Floating-point forward rounding-error refutation: the clause is the
    /// disjunction of the NEGATED premises of an FP forward-error UNSAT — the
    /// `fp.isNormal` input facts, the `fp.to_real` magnitude bounds, and the
    /// refuted rounding-error goal comparison (e.g.
    /// `(>= (- (fp.to_real DAG) MIRROR) c)` over an RNE `fp.add/sub/mul/neg`
    /// dag). Uses Alethe rule `fp_forward_error`; validated by `ay-proof`,
    /// which independently re-derives the whole analysis from the clause in
    /// exact rational arithmetic: it re-mines the normality + magnitude
    /// enclosures, re-checks the RNE-only and no-overflow side conditions,
    /// re-runs the half-ulp (`r(M) = 2^(max(k-1,emin)-sb)`) enclosure/error
    /// propagation, re-normalizes the goal polynomial against the exact
    /// mirror, and accepts ONLY if the certified bound strictly contradicts
    /// the claim constant (fail-closed on anything unrecognized). The variant
    /// carries no payload on purpose — nothing about it is load-bearing for
    /// soundness; the checker re-derives everything from the clause.
    FpForwardError,

    /// Pure nonlinear-real-arithmetic refutation by bounded exact-rational
    /// interval propagation (HC4-style contract/evaluate).
    ///
    /// The claim: the NEGATION of this clause is a conjunction of polynomial
    /// sign constraints (`<`, `<=`, `>`, `>=`, `=`, and negated-equality)
    /// over Real/Int-sorted terms, at least one monomial is genuinely
    /// nonlinear (total degree >= 2), and the checker's OWN bounded
    /// exact-rational interval-propagation kernel refutes the conjunction —
    /// proving it has no real solution, so the clause is valid in the theory
    /// of reals. Int-sorted variables are relaxed to range over R
    /// (R-infeasible implies Z-infeasible), and any non-whitelisted Real/Int
    /// application is abstracted as an opaque universally-quantified leaf.
    ///
    /// The variant carries NO payload on purpose: `ay-proof` re-decides the
    /// whole refutation from the clause terms alone, so there is nothing to
    /// forge. Any shape, sort, budget, or precision surprise fails closed
    /// (reject), never open. Alethe has no rule for this internal
    /// certificate, so it renders as an honest `hole` on that wire.
    NraIntervalUnsat,

    /// Pure nonlinear-real-arithmetic refutation of a UNIVARIATE polynomial
    /// constraint system by the checker's own exact Sturm-based cell
    /// decomposition.
    ///
    /// The claim: the NEGATION of this clause is a conjunction of polynomial
    /// sign constraints in exactly ONE variable (opaque leaves included),
    /// at least one monomial has degree >= 2, and the checker's OWN
    /// `BigRational` Sturm decision (square-free parts, root isolation with
    /// Cauchy bounds, algebraic at-root sign determination via gcd chains,
    /// sign-invariant cell scan) proves the conjunction infeasible over the
    /// reals — the complete univariate case analysis, valid at irrational
    /// roots too, so the clause is valid in the theory of reals.
    ///
    /// One documented widening (shared with [`Self::NraIntervalUnsat`]): a
    /// conjunct that normalizes to a FALSE constant refutes the conjunction
    /// outright, and is accepted before the one-variable shape check — such
    /// a clause may be multivariate. The refutation is the false constant
    /// itself, so soundness is unaffected.
    ///
    /// The variant carries NO payload on purpose: `ay-proof` re-decides the
    /// whole refutation from the clause terms alone. Any shape, sort,
    /// degree, or budget surprise fails closed (reject), never open. Alethe
    /// has no rule for this internal certificate, so it renders as an honest
    /// `hole` on that wire.
    NraUnivariateUnsat,

    /// Generic/unspecified (uses `trust` rule)
    #[default]
    Generic,

    /// Fixed-domain axiom for SMT-LIB's built-in five-element
    /// `RoundingMode` sort.
    ///
    /// Accepted instances are checked independently against the exact
    /// `{RNE, RNA, RTP, RTN, RTZ}` domain: either a disequality between two
    /// distinct mode literals, the conjunction containing every such
    /// pairwise disequality, or total coverage of one RoundingMode-sorted term
    /// by all five literals. It also accepts the complete pigeonhole theorem
    /// that six or more RoundingMode-sorted values cannot all be distinct.
    /// Uses AY's `fp_rounding_mode_domain` proof rule.
    RoundingModeDomain,
}

impl TheoryLemmaKind {
    /// Get the Alethe rule name for this lemma kind
    #[must_use]
    pub fn alethe_rule(&self) -> &'static str {
        match self {
            Self::EufTransitive => "eq_transitive",
            Self::EufReflexive => "eq_reflexive",
            Self::EufCongruent => "eq_congruent",
            Self::EufCongruentPred => "eq_congruent_pred",
            Self::LraFarkas => "la_generic",
            Self::LiaGeneric => "lia_generic",
            Self::LiaModRange => "lia_mod_range",
            Self::BvBitBlast | Self::BvBitBlastGate { .. } => "bv_bitblast",
            Self::ArraySelectStore { index_eq: true } => "read_over_write_pos",
            Self::ArraySelectStore { index_eq: false } => "read_over_write_neg",
            Self::ArrayStorePermutation => "store_permutation",
            Self::ArrayRowChain => "read_over_write_chain",
            Self::ArrayDefaultConst => "array_default_const",
            Self::SetCardNonNegative => "set_card_non_negative",
            Self::SetCardMemberLowerBound => "set_card_member_lower_bound",
            Self::SetCardEmpty => "set_card_empty",
            Self::SetCardMemberCount => "set_card_member_count",
            Self::SetCardEmptyByAssertion => "set_card_empty_by_assertion",
            Self::ArrayExtensionality => "extensionality",
            Self::FpToBv { .. } => "fp_to_bv",
            Self::StringLengthAxiom => "string_length",
            Self::StringLengthLemma => "string_length_lemma",
            Self::StringContentAxiom => "string_decompose",
            Self::StringNormalForm => "string_code_inj",
            Self::StringGroundEval => "string_ground_eval",
            Self::RegexIntersectEmpty => "regex_intersect_empty",
            Self::DatatypeDistinct => "dt_distinct",
            Self::DatatypeSelectorProject => "dt_project",
            Self::DatatypeTesterEval => "dt_tester",
            Self::OrderIteTautology => "order_ite_tautology",
            Self::BoolTautology => "bool_tautology",
            Self::IteSame => "ite_same",
            Self::FpClassification { .. } => "fp_classification",
            Self::FpRoundingModeDomain => "fp_rm_domain",
            Self::FpForwardError => "fp_forward_error",
            Self::NraIntervalUnsat => "nra_interval_unsat",
            Self::NraUnivariateUnsat => "nra_univariate_unsat",
            Self::Generic => "trust",
            Self::RoundingModeDomain => "fp_rounding_mode_domain",
        }
    }

    /// The rule name that may be written into an emitted Alethe proof.
    ///
    /// [`Self::alethe_rule`] is the *internal* identity and keeps returning
    /// `"trust"` for [`Self::Generic`] and the theory-specific names
    /// (`dt_distinct`, `read_over_write_pos`, `string_length`, …) that AY's
    /// own classifiers, dedup keys and `#8821` diagnostics match on. This
    /// method is the *wire* identity: kinds the Alethe checker does not
    /// implement render as `hole`, which the checker accepts as an honest
    /// unproved step, instead of an unknown rule name that voids the whole
    /// certificate.
    ///
    /// This does not hide anything from AY's soundness gates, which read the
    /// proof IR: `terminal_trust` flags `AletheRule::Hole` and
    /// `TheoryLemmaKind::is_trust()` identically, and `is_trust()` below is
    /// unchanged.
    #[must_use]
    pub fn alethe_wire_rule(&self) -> &str {
        wire_rule_name(self.alethe_rule())
    }

    /// True if this theory lemma kind exports as `trust` in Alethe format.
    ///
    /// Used by proof quality metrics to count theory lemmas that contribute
    /// unverified trust steps (#5657).
    #[must_use]
    pub fn is_trust(&self) -> bool {
        matches!(self, Self::Generic)
    }
}

/// Proof annotation for a theory lemma clause in the SAT clause trace (#6031 Phase 4).
///
/// Parallel to `ClausificationProof`: when the SAT clause trace contains an
/// "original" clause that was actually a theory lemma (added via `add_theory_lemma`),
/// this annotation tells `SatProofManager` to emit a `TheoryLemma` proof step
/// instead of the generic `assume + or` pattern.
#[derive(Debug, Clone)]
pub struct TheoryLemmaProof {
    /// The lemma clause in the exact order used when its positional
    /// annotations were produced. SAT watched-literal movement may permute a
    /// traced copy, so consumers must rebind annotations by literal identity
    /// rather than zipping them with the trace order.
    pub clause: Vec<TermId>,
    /// The kind of theory lemma (determines the Alethe rule)
    pub kind: TheoryLemmaKind,
    /// Optional Farkas coefficients for arithmetic theories
    pub farkas: Option<FarkasAnnotation>,
    /// Optional LIA-specific annotation (bounds gap, divisibility, cutting plane)
    pub lia: Option<LiaAnnotation>,
}

/// A proof step (Alethe-compatible)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofStep {
    /// Input assertion from the problem
    Assume(TermId),

    /// Resolution inference (SAT solver)
    Resolution {
        /// The resolvent clause (result of resolution)
        clause: Vec<TermId>,
        /// Pivot literal (resolved on)
        pivot: TermId,
        /// First clause premise
        clause1: ProofId,
        /// Second clause premise
        clause2: ProofId,
    },

    /// Theory lemma (from theory solver)
    TheoryLemma {
        /// Theory name (e.g., "EUF", "LRA", "LIA", "BV")
        theory: String,
        /// The lemma clause (disjunction of literals)
        clause: Vec<TermId>,
        /// Farkas coefficients for arithmetic theories (LRA/LIA)
        /// Used for Craig interpolation
        farkas: Option<FarkasAnnotation>,
        /// Kind of lemma (determines Alethe rule)
        kind: TheoryLemmaKind,
        /// Optional LIA-specific annotation (bounds gap, divisibility, cutting plane)
        lia: Option<LiaAnnotation>,
    },

    /// Generic proof step (Alethe-style)
    Step {
        /// The rule name (e.g., "trans", "cong", "and", "resolution")
        rule: AletheRule,
        /// The conclusion clause (disjunction of literals)
        clause: Vec<TermId>,
        /// Premise step IDs
        premises: Vec<ProofId>,
        /// Additional arguments (rule-specific)
        args: Vec<TermId>,
    },

    /// Subproof anchor (start of nested proof)
    Anchor {
        /// The step that ends this subproof
        end_step: ProofId,
        /// Variables introduced in this subproof
        variables: Vec<(String, crate::sort::Sort)>,
    },
}

pub use crate::alethe::{
    is_checkable_alethe_rule, wire_rule_name, AletheRule, CHECKABLE_ALETHE_RULES,
    UNPROVED_STEP_RULE,
};

/// Proof step identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ProofId(pub u32);

impl std::fmt::Display for ProofId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// A complete proof (Alethe-compatible)
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct Proof {
    /// Proof steps
    pub steps: Vec<ProofStep>,
    /// Named step IDs (for assume commands)
    pub named_steps: crate::kani_compat::KaniHashMap<String, ProofId>,
}

impl Proof {
    /// Create a new empty proof
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Rebuild a proof from an ordered list of steps, leaving `named_steps`
    /// empty. `ProofId(i)` resolves to `steps[i]` (the same positional invariant
    /// [`add_step`](Self::add_step) maintains), so the step DAG is preserved.
    /// `named_steps` only resolves `assume` *names* for the Alethe printer and is
    /// never consulted by [`check_proof`](crate) / `check_proof_strict`, so a
    /// proof rebuilt this way re-checks identically. This is the deserialization
    /// counterpart used to reconstruct a [`Proof`] from a serialized step list.
    #[must_use]
    pub fn from_steps(steps: Vec<ProofStep>) -> Self {
        Self {
            steps,
            named_steps: crate::kani_compat::KaniHashMap::default(),
        }
    }

    /// Add a proof step
    #[allow(clippy::cast_possible_truncation)] // Proof step count is bounded well under u32::MAX
    pub fn add_step(&mut self, step: ProofStep) -> ProofId {
        debug_assert!(
            self.steps.len() < u32::MAX as usize,
            "BUG: proof exceeds u32::MAX steps ({})",
            self.steps.len()
        );
        let id = ProofId(self.steps.len() as u32);
        self.steps.push(step);
        id
    }

    /// Add an assumption and optionally name it
    pub fn add_assume(&mut self, term: TermId, name: Option<String>) -> ProofId {
        let id = self.add_step(ProofStep::Assume(term));
        if let Some(n) = name {
            self.named_steps.insert(n, id);
        }
        id
    }

    /// Add a generic step with a rule
    pub fn add_rule_step(
        &mut self,
        rule: AletheRule,
        clause: Vec<TermId>,
        premises: Vec<ProofId>,
        args: Vec<TermId>,
    ) -> ProofId {
        self.add_step(ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        })
    }

    /// Add a resolution step
    pub fn add_resolution(
        &mut self,
        clause: Vec<TermId>,
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
    ) -> ProofId {
        self.add_step(ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        })
    }

    /// Add a theory lemma with default kind
    pub fn add_theory_lemma(&mut self, theory: impl Into<String>, clause: Vec<TermId>) -> ProofId {
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        })
    }

    /// Add a theory lemma with specified kind
    pub fn add_theory_lemma_with_kind(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        debug_assert!(
            !matches!(kind, TheoryLemmaKind::LraFarkas),
            "BUG: LraFarkas requires Farkas :args; use add_theory_lemma_with_farkas_and_kind"
        );
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: None,
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with Farkas annotation (for arithmetic theories)
    pub fn add_theory_lemma_with_farkas(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
    ) -> ProofId {
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    /// Add a theory lemma with Farkas annotation and explicit kind
    pub fn add_theory_lemma_with_farkas_and_kind(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: FarkasAnnotation,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        // Farkas certificates must have non-negative coefficients.
        // A negative coefficient indicates a bug in the arithmetic solver's
        // conflict explanation. Catch early before emitting into the proof.
        debug_assert!(
            farkas.is_valid(),
            "BUG: Farkas certificate has negative coefficient(s): {:?}",
            farkas.coefficients,
        );
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas: Some(farkas),
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with optional Farkas annotation and explicit kind (#6031 Phase 4).
    ///
    /// Like `add_theory_lemma_with_farkas_and_kind` but accepts `Option<FarkasAnnotation>`,
    /// used by `SatProofManager` when wiring theory lemma annotations from the clause trace.
    pub fn add_theory_lemma_with_farkas_and_kind_opt(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: Option<FarkasAnnotation>,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        if let Some(ref f) = farkas {
            debug_assert!(
                f.is_valid(),
                "BUG: Farkas certificate has negative coefficient(s): {:?}",
                f.coefficients,
            );
        }
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas,
            kind,
            lia: None,
        })
    }

    /// Add a theory lemma with LIA annotation and explicit kind.
    ///
    /// Used by the LIA solver when it can provide a specific proof shape
    /// (bounds gap, divisibility, or cutting plane).
    pub fn add_theory_lemma_with_lia(
        &mut self,
        theory: impl Into<String>,
        clause: Vec<TermId>,
        farkas: Option<FarkasAnnotation>,
        kind: TheoryLemmaKind,
        lia: LiaAnnotation,
    ) -> ProofId {
        if let Some(ref f) = farkas {
            debug_assert!(
                f.is_valid(),
                "BUG: Farkas certificate has negative coefficient(s): {:?}",
                f.coefficients,
            );
        }
        self.add_step(ProofStep::TheoryLemma {
            theory: theory.into(),
            clause,
            farkas,
            kind,
            lia: Some(lia),
        })
    }

    /// Get a step by ID
    #[must_use]
    pub fn get_step(&self, id: ProofId) -> Option<&ProofStep> {
        self.steps.get(id.0 as usize)
    }

    /// Get the number of steps
    #[must_use]
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Check if the proof is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "proof_tests.rs"]
mod tests;
