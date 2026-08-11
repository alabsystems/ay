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

/// Rule names the Alethe proof checker actually implements.
///
/// This is the *wire* allowlist: a `:rule` name outside this set is not a
/// proof at all — carcara rejects the whole document with
/// `CheckerError::UnknownRule` and reports `invalid`, which is strictly worse
/// than declaring the step unproved. See [`AletheRule::wire_name`].
///
/// Provenance (do not hand-edit; regenerate against the checker you ship
/// against). Every entry below was verified against the installed
/// `carcara 1.1.0 [git main 9a352ee]` by probing each candidate name:
///
/// ```text
/// printf '(assume h1 p)\n(assume h2 (not p))\n(step t1 (cl) :rule NAME :premises (h1 h2))\n' > t.alethe
/// carcara check t.alethe prob.smt2   # "unknown rule" <=> NAME is not in this table
/// ```
///
/// The probe is deliberately empirical rather than scraped from carcara's
/// `get_rule` source: a source scrape of that `match` also yields `eq_mp`,
/// which the shipped binary rejects. A table that is too *permissive* emits
/// `invalid` proofs, so it is derived from the checker's observed behaviour.
///
/// ONE ENTRY IS AHEAD OF UPSTREAM: `dt_clash` (datatype constructor
/// distinctness) is implemented in the datatype-enabled carcara build
/// (`carcara/src/checker/rules/datatypes.rs`), not in `carcara 1.1.0
/// [git main 9a352ee]`. Against a checker without it, a `dt_clash` step is an
/// unknown rule and the document is `invalid` rather than `holey` — see
/// [`wire_rule_name`] for why that trade is taken.
///
/// MUST stay sorted — [`is_checkable_alethe_rule`] binary-searches it.
pub const CHECKABLE_ALETHE_RULES: [&str; 183] = [
    "ac_simp",
    "aci_simp",
    "and",
    "and_intro",
    "and_neg",
    "and_pos",
    "and_simplify",
    "arrays_ext",
    "arrays_idx",
    "arrays_row",
    "arrays_row_contra",
    "bfun_elim",
    "bind",
    "bind_let",
    "bitblast_add",
    "bitblast_and",
    "bitblast_ashr",
    "bitblast_comp",
    "bitblast_concat",
    "bitblast_const",
    "bitblast_equal",
    "bitblast_extract",
    "bitblast_lshr",
    "bitblast_mult",
    "bitblast_neg",
    "bitblast_not",
    "bitblast_or",
    "bitblast_shl",
    "bitblast_sign_extend",
    "bitblast_slt",
    "bitblast_udiv",
    "bitblast_ult",
    "bitblast_urem",
    "bitblast_var",
    "bitblast_xnor",
    "bitblast_xor",
    "bool_simplify",
    "bounded_farkas",
    "comp_simplify",
    "concat_conflict",
    "concat_cprop_prefix",
    "concat_cprop_suffix",
    "concat_csplit_prefix",
    "concat_csplit_suffix",
    "concat_eq",
    "concat_lprop_prefix",
    "concat_lprop_suffix",
    "concat_split_prefix",
    "concat_split_suffix",
    "concat_unify",
    "cong",
    "connective_def",
    "contraction",
    "cp_addition",
    "cp_division",
    "cp_literal",
    "cp_multiplication",
    "cp_normalize",
    "cp_saturation",
    "distinct_elim",
    "div_simplify",
    "drat",
    "drup",
    "dt_clash",
    "eq_congruent",
    "eq_congruent_pred",
    "eq_reflexive",
    "eq_simplify",
    "eq_symmetric",
    "eq_transitive",
    "equiv1",
    "equiv2",
    "equiv_neg1",
    "equiv_neg2",
    "equiv_pos1",
    "equiv_pos2",
    "equiv_simplify",
    "evaluate",
    "false",
    "forall_inst",
    "ho_cong",
    "hole",
    "implies",
    "implies_neg1",
    "implies_neg2",
    "implies_pos",
    "implies_simplify",
    "ite1",
    "ite2",
    "ite_intro",
    "ite_neg1",
    "ite_neg2",
    "ite_pos1",
    "ite_pos2",
    "ite_simplify",
    "la_disequality",
    "la_generic",
    "la_mult_neg",
    "la_mult_pos",
    "la_rw_eq",
    "la_tautology",
    "la_totality",
    "let",
    "lia_generic",
    "miniscope_distribute",
    "miniscope_ite",
    "miniscope_split",
    "minus_simplify",
    "mod_simplify",
    "nary_elim",
    "not_and",
    "not_equiv1",
    "not_equiv2",
    "not_implies1",
    "not_implies2",
    "not_ite1",
    "not_ite2",
    "not_not",
    "not_or",
    "not_simplify",
    "not_symm",
    "not_xor1",
    "not_xor2",
    "onepoint",
    "or",
    "or_neg",
    "or_pos",
    "or_simplify",
    "pbblast_bvand",
    "pbblast_bvand_ith_bit",
    "pbblast_bveq",
    "pbblast_bvsge",
    "pbblast_bvsgt",
    "pbblast_bvsle",
    "pbblast_bvslt",
    "pbblast_bvuge",
    "pbblast_bvugt",
    "pbblast_bvule",
    "pbblast_bvult",
    "pbblast_bvxor",
    "pbblast_bvxor_ith_bit",
    "pbblast_pbbconst",
    "pbblast_pbbvar",
    "poly_simp",
    "poly_simp_rel",
    "prod_simplify",
    "qnt_cnf",
    "qnt_join",
    "qnt_rm_unused",
    "qnt_simplify",
    "rare_rewrite",
    "re_concat_unfold_pos",
    "re_inter",
    "re_kleene_star_unfold_pos",
    "re_unfold_neg",
    "re_unfold_neg_concat_fixed_prefix",
    "re_unfold_neg_concat_fixed_suffix",
    "refl",
    "reordering",
    "resolution",
    "shuffle",
    "sko_ex",
    "sko_forall",
    "strict_refl",
    "strict_resolution",
    "string_decompose",
    "string_length_non_empty",
    "string_length_pos",
    "subproof",
    "sum_simplify",
    "symm",
    "tautology",
    "th_resolution",
    "trans",
    "true",
    "unary_minus_simplify",
    "weakening",
    "xor1",
    "xor2",
    "xor_neg1",
    "xor_neg2",
    "xor_pos1",
    "xor_pos2",
];

/// The Alethe rule name used for a step whose justification is not being
/// claimed: an honest, checker-accepted placeholder.
///
/// carcara accepts `hole` and marks the document `holey` (see its
/// `check_step`: `hole` short-circuits to `Ok(())` and sets `is_holey`), so a
/// `hole` step is machine-readable as "this solver did not prove this",
/// whereas an invented rule name is indistinguishable from a typo and voids
/// the entire certificate.
///
/// This is an EMISSION concern only. AY's publication soundness gates validate
/// the proof IR, not the printed name. Direct `AletheRule::Hole`/`Trust` steps
/// are counted by `terminal_trust::TerminalTrustReport`. A natively checked
/// theory kind may also map to a wire `hole` when the pinned external calculus
/// lacks that inference; in that case the native strict verdict remains valid,
/// while artifact disclosure and `restricted_rule_subset` report that the Alethe text
/// is only a holey diagnostic skeleton. Neither case can become an externally
/// `valid` certificate by renaming the wire rule.
pub const UNPROVED_STEP_RULE: &str = "hole";

/// Internal rule names that are SPELLED differently by the checker.
///
/// Each pair is `(internal, wire)` where the two names denote the SAME
/// inference — this is a spelling translation, never a change of claim. An
/// entry is admissible only when the checker's rule accepts exactly (or a
/// subset of) the clauses AY's kind is allowed to carry, so that a step AY
/// emits under `internal` is one the checker can independently re-derive.
///
/// * `dt_distinct` → `dt_clash`: datatype constructor distinctness, "two
///   applications of different constructors of one datatype cannot be equal".
///   AY's [`crate::proof::TheoryLemmaKind::DatatypeDistinct`] is assigned only
///   by `ay_proof::recognize_datatype_distinct`, which accepts the unit
///   disjointness clause `(cl (not (= C1(..) C2(..))))` and the binary
///   exclusion clause `(cl (not (= t C1(..))) (not (= t C2(..))))` with both
///   heads registered constructors of the same datatype and different from
///   each other. carcara's `dt_clash` accepts those two shapes and nothing
///   else, re-deriving constructor membership from the problem's own
///   `declare-datatypes` rather than trusting AY's registry. The two
///   validators are therefore independent and shape-aligned.
const WIRE_RULE_ALIASES: [(&str, &str); 1] = [("dt_distinct", "dt_clash")];

/// True if the Alethe checker implements `name`, i.e. emitting it produces a
/// checked step rather than `invalid`.
#[must_use]
pub fn is_checkable_alethe_rule(name: &str) -> bool {
    CHECKABLE_ALETHE_RULES.binary_search(&name).is_ok()
}

/// Map an internal rule name to the name that may be written into a proof.
///
/// Returns `name` unchanged when the checker implements it, its
/// [`WIRE_RULE_ALIASES`] spelling when the checker implements the same
/// inference under another name, and [`UNPROVED_STEP_RULE`] otherwise. Never
/// invents a rule name and never substitutes a *different* inference: claiming
/// `arrays_ext` for a step that is not an `arrays_ext` inference would fail the
/// checker just as loudly, and claiming it for one that happens to pass would
/// be a false certificate.
///
/// The `dt_distinct` → `dt_clash` alias is the one place where the wire name is
/// AHEAD of the upstream checker: a carcara build without the datatype rules
/// answers `unknown rule` and marks the whole document `invalid`, which is
/// worse than the `hole` this used to print. The trade is taken deliberately —
/// `hole` can never become `valid`, so a datatype refutation could never be
/// externally certified at all, and the alias is a one-line revert. It costs
/// nothing in soundness either way: AY's own gates read the proof IR, where
/// `TheoryLemmaKind::DatatypeDistinct` is re-validated by
/// `ay_proof::validate_datatype_distinct` regardless of what is printed.
#[must_use]
pub fn wire_rule_name(name: &str) -> &str {
    if is_checkable_alethe_rule(name) {
        return name;
    }
    if let Some((_, wire)) = WIRE_RULE_ALIASES.iter().find(|(from, _)| *from == name) {
        return wire;
    }
    UNPROVED_STEP_RULE
}

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

    /// The rule name that may be written into an emitted Alethe proof.
    ///
    /// [`Self::name`] is the *internal* identity: soundness gates, dedup keys
    /// and quality metrics match on it and must keep seeing `"trust"` for
    /// [`Self::Trust`]. This method is the *wire* identity, and is the only
    /// one a printer may use. Variants the checker does not implement
    /// (`trust`, `extensionality`, `read_over_write_*`, `all_simplify`,
    /// `equiv`, `ite`, `not_true`, `not_false`, …) render as
    /// [`UNPROVED_STEP_RULE`] so the document checks as *holey* instead of
    /// being thrown out as *invalid*.
    ///
    /// Steps that genuinely are a real Alethe inference are unaffected: the
    /// printer's dedicated lowerings (`arrays_ext`, `arrays_row`,
    /// `arrays_idx`, `la_generic`, `eq_transitive`, `distinct_elim`, …) build
    /// checkable rule names directly and pass through here unchanged.
    #[must_use]
    pub fn wire_name(&self) -> &str {
        wire_rule_name(self.name())
    }
}

impl std::fmt::Display for AletheRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[cfg(test)]
mod wire_name_tests {
    use super::*;
    use crate::proof::TheoryLemmaKind;

    #[test]
    fn table_is_sorted_and_deduplicated() {
        // `is_checkable_alethe_rule` binary-searches, so an unsorted or
        // duplicated table would silently start answering "not checkable" for
        // real rules and downgrade valid proofs to holey.
        let mut sorted = CHECKABLE_ALETHE_RULES;
        sorted.sort_unstable();
        assert_eq!(CHECKABLE_ALETHE_RULES, sorted, "table must stay sorted");
        let mut seen = std::collections::HashSet::new();
        for name in CHECKABLE_ALETHE_RULES {
            assert!(seen.insert(name), "duplicate rule name in table: {name}");
        }
    }

    #[test]
    fn every_alias_target_is_checkable_and_no_alias_is_dead() {
        for (internal, wire) in WIRE_RULE_ALIASES {
            // An alias whose target the checker does not implement would turn
            // an honest `hole` into an unknown rule name for nothing.
            assert!(
                is_checkable_alethe_rule(wire),
                "alias target {wire} must be in the checkable table"
            );
            // An alias whose source is already checkable never fires (the
            // pass-through arm wins) and is silently misleading.
            assert!(
                !is_checkable_alethe_rule(internal),
                "alias source {internal} is already checkable; the alias is dead"
            );
            assert_eq!(wire_rule_name(internal), wire);
            assert_ne!(
                wire_rule_name(internal),
                UNPROVED_STEP_RULE,
                "{internal} must reach its checked spelling, not the hole"
            );
        }
    }

    #[test]
    fn hole_is_itself_checkable() {
        // The fallback must be a rule the checker implements, or the mapping
        // would turn one invalid proof into another.
        assert!(is_checkable_alethe_rule(UNPROVED_STEP_RULE));
        assert_eq!(wire_rule_name(UNPROVED_STEP_RULE), UNPROVED_STEP_RULE);
    }

    #[test]
    fn real_rules_pass_through_unchanged() {
        for name in [
            "resolution",
            "th_resolution",
            "eq_congruent",
            "eq_transitive",
            "la_generic",
            "lia_generic",
            "arrays_ext",
            "arrays_row",
            "arrays_idx",
            "distinct_elim",
            "cong",
            "subproof",
            "drup",
            "string_decompose",
        ] {
            assert_eq!(wire_rule_name(name), name, "{name} must not be rewritten");
        }
    }

    #[test]
    fn every_name_the_checker_rejects_becomes_hole() {
        // Measured against carcara 1.1.0 [git main 9a352ee]: each of these
        // names produces `unknown rule` and makes the whole document invalid.
        for name in [
            "trust",
            "dt_project",
            "dt_enum_pigeonhole",
            "all_simplify",
            "arith_simplify",
            "array_ext_diff_intro",
            "bool_tautology",
            "bv_bitblast",
            "equiv",
            "extensionality",
            "fp_classification",
            "fp_rm_domain",
            "fp_rounding_mode_domain",
            "fp_to_bv",
            "ite",
            "ite_same",
            "lra_farkas",
            "nia_positivstellensatz",
            "not_false",
            "not_true",
            "nra_interval_unsat",
            "nra_positivstellensatz",
            "nra_univariate_unsat",
            "read_over_write_chain",
            "read_over_write_neg",
            "read_over_write_pos",
            "regex_intersect_empty",
            "store_permutation",
            "string_code_inj",
            "string_ground_eval",
            "string_length",
            "string_length_lemma",
            "eq_mp",
        ] {
            assert!(
                !is_checkable_alethe_rule(name),
                "{name} must not be in the checkable table"
            );
            assert_eq!(
                wire_rule_name(name),
                UNPROVED_STEP_RULE,
                "{name} must render as an honest hole, never as an unknown rule"
            );
        }
    }

    #[test]
    fn trust_renders_as_hole_but_keeps_its_internal_identity() {
        // The soundness gates (terminal-trust, quality metrics, dedup keys)
        // match on the INTERNAL name; only the wire name changes.
        assert_eq!(AletheRule::Trust.name(), "trust");
        assert_eq!(AletheRule::Trust.wire_name(), "hole");
        assert_eq!(TheoryLemmaKind::Generic.alethe_rule(), "trust");
        assert_eq!(TheoryLemmaKind::Generic.alethe_wire_rule(), "hole");
        assert!(TheoryLemmaKind::Generic.is_trust());

        // Datatype distinctness keeps its INTERNAL name and now prints the
        // checker's spelling of the same axiom (`dt_clash`), so the step is
        // genuinely checked instead of left as a hole.
        assert_eq!(
            TheoryLemmaKind::DatatypeDistinct.alethe_rule(),
            "dt_distinct"
        );
        assert_eq!(
            TheoryLemmaKind::DatatypeDistinct.alethe_wire_rule(),
            "dt_clash"
        );

        // Finite-enum exhaustiveness is checked only by AY's native strict
        // checker. The pinned external Alethe calculus has no equivalent rule,
        // so the wire format must disclose the gap as a hole.
        assert_eq!(
            TheoryLemmaKind::DatatypeEnumPigeonhole.alethe_rule(),
            "dt_enum_pigeonhole"
        );
        assert_eq!(
            TheoryLemmaKind::DatatypeEnumPigeonhole.alethe_wire_rule(),
            "hole"
        );
        assert!(!is_checkable_alethe_rule("dt_enum_pigeonhole"));

        // A theory lemma that DOES have a real Alethe rule keeps it.
        assert_eq!(TheoryLemmaKind::LraFarkas.alethe_wire_rule(), "la_generic");
        assert_eq!(
            TheoryLemmaKind::LiaGeneric.alethe_wire_rule(),
            "lia_generic"
        );
    }
}
