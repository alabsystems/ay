// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe proof rules.
//!
//! The Alethe format (used by the carcara proof checker) defines rules
//! for each logical inference step.  This module houses the [`AletheRule`]
//! enum and its string-name conversion, extracted from `proof.rs` for
//! code health (#5970).
//!
//! Reference: <https://github.com/ufmg-smite/carcara>

/// Alethe proof rules
///
/// These rules correspond to the rules supported by carcara.
/// See: <https://github.com/ufmg-smite/carcara>
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[non_exhaustive]
pub enum AletheRule {
    // === Boolean rules ===
    /// True introduction
    True,
    /// False elimination
    False,
    /// Negation of true
    NotTrue,
    /// Negation of false
    NotFalse,
    /// And introduction
    And,
    /// And elimination (position i)
    AndPos(u32),
    /// And negation
    AndNeg,
    /// Not-and
    NotAnd,
    /// Or introduction
    Or,
    /// Or elimination (position i)
    OrPos(u32),
    /// Or negation
    OrNeg,
    /// Not-or
    NotOr,
    /// Implication introduction
    Implies,
    /// Implication negation 1
    ImpliesNeg1,
    /// Implication negation 2
    ImpliesNeg2,
    /// Not-implies 1
    NotImplies1,
    /// Not-implies 2
    NotImplies2,
    /// Equivalence introduction
    Equiv,
    /// Equivalence positive 1
    EquivPos1,
    /// Equivalence positive 2
    EquivPos2,
    /// Equivalence negative 1
    EquivNeg1,
    /// Equivalence negative 2
    EquivNeg2,
    /// Not-equivalence 1
    NotEquiv1,
    /// Not-equivalence 2
    NotEquiv2,
    /// ITE introduction
    Ite,
    /// ITE positive 1
    ItePos1,
    /// ITE positive 2
    ItePos2,
    /// ITE negative 1
    IteNeg1,
    /// ITE negative 2
    IteNeg2,
    /// Not-ITE 1
    NotIte1,
    /// Not-ITE 2
    NotIte2,
    /// ITE elimination 1: premise `(cl (ite c a b))` ⊢ `(cl c b)`
    Ite1,
    /// ITE elimination 2: premise `(cl (ite c a b))` ⊢ `(cl (not c) a)`
    Ite2,
    /// Term-ITE introduction: ⊢ `(cl (= t (and t (ite c (= s a) (= s b)))))`
    /// where `s = (ite c a b)` is a term-level ite occurring in `t`
    IteIntro,

    // === XOR tautology rules (Tseitin clausification) ===
    /// XOR positive 1: (cl (not (xor p q)) p q)
    XorPos1,
    /// XOR positive 2: (cl (not (xor p q)) (not p) (not q))
    XorPos2,
    /// XOR negative 1: (cl (xor p q) p (not q))
    XorNeg1,
    /// XOR negative 2: (cl (xor p q) (not p) q)
    XorNeg2,

    // === Implies tautology rule (Tseitin clausification) ===
    /// Implies positive: (cl (not (=> p q)) (not p) q)
    ImpliesPos,

    // === Resolution ===
    /// Propositional resolution
    Resolution,
    /// Theory resolution (resolution on theory literals)
    ThResolution,
    /// Contraction (remove duplicate literals)
    Contraction,
    /// Weakening (append extra literals: the premise clause is a prefix of
    /// the conclusion)
    Weakening,

    // === Equality ===
    /// Reflexivity: t = t
    Refl,
    /// Symmetry: a = b => b = a
    Symm,
    /// Transitivity: a = b, b = c => a = c
    Trans,
    /// Congruence: f(a) = f(b) if a = b
    Cong,
    /// Equality reflexivity (eq_reflexive)
    EqReflexive,
    /// Equality symmetry tautology: `(cl (= (= a b) (= b a)))`
    EqSymmetric,
    /// Equality transitive
    EqTransitive,
    /// Equality congruent
    EqCongruent,
    /// Equality congruent predicate
    EqCongruentPred,
    /// Distinct elimination: (= (distinct t1 .. tn) <pairwise-disequality expansion>)
    DistinctElim,

    // === Arithmetic ===
    /// Linear arithmetic tautology
    LaTautology,
    /// Linear arithmetic generic
    LaGeneric,
    /// Linear arithmetic disequality
    LaDisequality,
    /// Linear arithmetic totality
    LaTotality,
    /// Multiply by positive
    LaMultPos,
    /// Multiply by negative
    LaMultNeg,
    /// Linear integer arithmetic generic (SMT calls LIA solver)
    LiaGeneric,

    // === Quantifiers ===
    /// Forall instantiation
    ForallInst,
    /// Skolemization
    Skolem,

    // === Subproof rules ===
    /// Subproof (nested proof)
    Subproof,
    /// Bind (variable binding)
    Bind,

    // === Simplification ===
    /// Generic simplification
    AllSimplify,
    /// Boolean simplification
    BoolSimplify,
    /// Arithmetic simplification
    ArithSimplify,

    // === Bitvector ===
    /// BV bit-blast: propositional encoding of a bitvector operation.
    ///
    /// The conclusion clause encodes the gate semantics as CNF.
    /// Per CVC5 convention, the rule name is `bv_bitblast`.
    BvBitblast,

    // === Array theory ===
    /// Read-over-write positive: indices equal.
    ///
    /// `(= (select (store a i v) i) v)`
    ReadOverWritePos,
    /// Read-over-write negative: indices not equal.
    ///
    /// `(=> (not (= i j)) (= (select (store a i v) j) (select a j)))`
    ReadOverWriteNeg,
    /// Store permutation (n-ary store-commutativity): two `store` chains over
    /// the same base writing the same `(index, value)` multiset are equal when
    /// the indices are pairwise distinct.
    StorePermutation,
    /// Read-over-write evaluated through a `store` chain, optionally under an
    /// array-equality premise.
    ReadOverWriteChain,
    /// Extensionality: point-wise equal arrays are equal.
    ///
    /// `(=> (forall ((k Index)) (= (select a k) (select b k))) (= a b))`
    Extensionality,
    /// Array extensionality difference-witness INTRODUCTION (a definition,
    /// not an inference).
    ///
    /// Binds a fresh 0-ary symbol `k` — the Skolemization of the array theory's
    /// `diff` function at one concrete array pair — to the UNORDERED pair
    /// `{a, b}` it was minted for. The step carries NO conclusion clause (it
    /// contributes nothing to the derivation and can never be a premise); its
    /// entire content is the three `:args` `(k a b)`.
    ///
    /// Recording the introduction is what makes the Skolemized extensionality
    /// clause `(cl (= a b) (not (= (select a k) (select b k))))` certifiable:
    /// that clause is NOT a tautology, it is a conservative extension, and only
    /// a checker that can see the witness's provenance (bound once, to exactly
    /// this pair, over a symbol absent from the problem) can tell the two apart.
    /// See `ay-proof` `ExtDiffRegistry` for the checks and their soundness
    /// argument.
    ArrayExtDiffIntro,

    // === Floating-point ===
    /// FP to BV translation: IEEE 754 encoding faithfulness.
    ///
    /// The conclusion clause encodes the FP→BV lowering step. Composes
    /// with `BvBitblast`: FP operations are first lowered to BV circuits,
    /// then bit-blasted to propositional clauses.
    FpToBv,

    // === String theory ===
    /// String length axiom: `len(concat(a, b)) = len(a) + len(b)`, etc.
    StringLength,
    /// String decomposition: substr, contains, replace rewriting.
    StringDecompose,
    /// String code injectivity: `str.to_code` / `str.from_code` reasoning.
    StringCodeInj,

    // === Special ===
    /// Hole (placeholder, should be elaborated)
    Hole,
    /// DRUP (clause addition verified by unit propagation)
    Drup,
    /// Trust (unverified step)
    Trust,
    /// Custom rule (extension)
    Custom(String),
    /// Exact evaluation of a closed term.
    ///
    /// Appended to preserve serialized discriminants of the older variants.
    Evaluate,
}

impl AletheRule {
    /// Get the Alethe rule name as a string
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::True => "true",
            Self::False => "false",
            Self::NotTrue => "not_true",
            Self::NotFalse => "not_false",
            Self::And => "and",
            Self::AndPos(_) => "and_pos",
            Self::AndNeg => "and_neg",
            Self::NotAnd => "not_and",
            Self::Or => "or",
            Self::OrPos(_) => "or_pos",
            Self::OrNeg => "or_neg",
            Self::NotOr => "not_or",
            Self::Implies => "implies",
            Self::ImpliesNeg1 => "implies_neg1",
            Self::ImpliesNeg2 => "implies_neg2",
            Self::NotImplies1 => "not_implies1",
            Self::NotImplies2 => "not_implies2",
            Self::Equiv => "equiv",
            Self::EquivPos1 => "equiv_pos1",
            Self::EquivPos2 => "equiv_pos2",
            Self::EquivNeg1 => "equiv_neg1",
            Self::EquivNeg2 => "equiv_neg2",
            Self::NotEquiv1 => "not_equiv1",
            Self::NotEquiv2 => "not_equiv2",
            Self::Ite => "ite",
            Self::ItePos1 => "ite_pos1",
            Self::ItePos2 => "ite_pos2",
            Self::IteNeg1 => "ite_neg1",
            Self::IteNeg2 => "ite_neg2",
            Self::NotIte1 => "not_ite1",
            Self::NotIte2 => "not_ite2",
            Self::Ite1 => "ite1",
            Self::Ite2 => "ite2",
            Self::IteIntro => "ite_intro",
            Self::XorPos1 => "xor_pos1",
            Self::XorPos2 => "xor_pos2",
            Self::XorNeg1 => "xor_neg1",
            Self::XorNeg2 => "xor_neg2",
            Self::ImpliesPos => "implies_pos",
            Self::Resolution => "resolution",
            Self::ThResolution => "th_resolution",
            Self::Contraction => "contraction",
            Self::Weakening => "weakening",
            Self::Refl => "refl",
            Self::Symm => "symm",
            Self::Trans => "trans",
            Self::Cong => "cong",
            Self::EqReflexive => "eq_reflexive",
            Self::EqSymmetric => "eq_symmetric",
            Self::EqTransitive => "eq_transitive",
            Self::EqCongruent => "eq_congruent",
            Self::EqCongruentPred => "eq_congruent_pred",
            Self::DistinctElim => "distinct_elim",
            Self::LaTautology => "la_tautology",
            Self::LaGeneric => "la_generic",
            Self::LaDisequality => "la_disequality",
            Self::LaTotality => "la_totality",
            Self::LaMultPos => "la_mult_pos",
            Self::LaMultNeg => "la_mult_neg",
            Self::LiaGeneric => "lia_generic",
            Self::ForallInst => "forall_inst",
            Self::Skolem => "sko_forall",
            Self::Subproof => "subproof",
            Self::Bind => "bind",
            Self::AllSimplify => "all_simplify",
            Self::BoolSimplify => "bool_simplify",
            Self::ArithSimplify => "arith_simplify",
            Self::BvBitblast => "bv_bitblast",
            Self::ReadOverWritePos => "read_over_write_pos",
            Self::ReadOverWriteNeg => "read_over_write_neg",
            Self::StorePermutation => "store_permutation",
            Self::ReadOverWriteChain => "read_over_write_chain",
            Self::Extensionality => "extensionality",
            Self::ArrayExtDiffIntro => "array_ext_diff_intro",
            Self::FpToBv => "fp_to_bv",
            Self::StringLength => "string_length",
            Self::StringDecompose => "string_decompose",
            Self::StringCodeInj => "string_code_inj",
            Self::Hole => "hole",
            Self::Drup => "drup",
            Self::Trust => "trust",
            Self::Custom(name) => name,
            Self::Evaluate => "evaluate",
        }
    }
}

impl std::fmt::Display for AletheRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}
