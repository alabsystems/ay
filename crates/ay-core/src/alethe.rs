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

mod bare_rule_requirements;
pub use bare_rule_requirements::alethe_rule_requires_premises_or_args;
#[cfg(test)]
use bare_rule_requirements::PREMISE_OR_ARG_REQUIRED_ALETHE_RULES;

/// Rule names the in-process Alethe document checker accepts.
///
/// Production emission is the intersection of this compatibility vocabulary
/// with AY's built-in rule producers, plus checked aliases and direct printer
/// lowerings. A `:rule` name the installed external checker does not implement
/// makes its whole document `invalid`, which is strictly worse than declaring
/// the step unproved. See [`AletheRule::wire_name`].
///
/// Provenance (do not hand-edit; regenerate against the checker you ship
/// against). Except for the parser-only compatibility entry documented below,
/// every entry was verified against the installed
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
/// PARSER-ONLY COMPATIBILITY ENTRY: `dt_clash` remains in this document-checker
/// vocabulary, but production AY has no built-in rule with that spelling and
/// no alias targets it. The installed `carcara 1.1.0 [git master 9a352ee]`
/// answered `unknown rule` when probed on 2026-08-12, so the former
/// `dt_distinct` wire alias was reverted. Keeping this parser entry is
/// intentionally separate from the wire inventory: the standing emission
/// probe in `ay-proof/tests/wire_rule_coverage.rs` scans the pass-throughs AY
/// actually selects, alias targets, and direct printer lowerings.
///
/// MUST stay sorted — [`is_checkable_alethe_rule`] binary-searches it.
pub const CHECKABLE_ALETHE_RULES: [&str; 182] = [
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
/// There are currently no aliases. `dt_distinct` → `dt_clash` was reverted on
/// 2026-08-12 after the installed `carcara 1.1.0 [git master 9a352ee]` probe
/// returned `invalid` and `checking failed on step 't0' with rule 'dt_clash':
/// unknown rule`. The assumed newer datatype rule was not in the checker AY
/// actually ships against. Keeping `dt_distinct` as an honest `hole` is
/// strictly better: `holey` identifies one unproved step, while `invalid`
/// discredits the entire document. A future alias must pass the installed
/// checker probe in `ay-proof/tests/wire_rule_coverage.rs` as well as the
/// inference-shape admissibility argument above.
///
/// MEASURED NON-ALIAS: `bv_bitblast`. The checker DOES implement bit-blasting
/// — `bitblast_add|and|ashr|comp|concat|const|equal|extract|lshr|mult|neg|not|
/// or|shl|sign_extend|slt|udiv|ult|urem|var|xnor|xor` are all live in the
/// pinned build — but not as anything a rename could reach. Every one of those
/// rules concludes `(= <word-level term> (@bbterm b0 .. bn))`, i.e. it pairs a
/// bit-vector term with an EXPLICIT list of Boolean bit terms, whereas an AY
/// [`crate::proof::TheoryLemmaKind::BvBitBlast`] clause is a word-level
/// tautology containing no `@bbterm` at all. Aliasing the coarse kind onto any
/// per-operator name would therefore be rejected by the checker, and aliasing
/// it onto a name whose inference it is not would be a false certificate. The
/// coarse kind stays `hole` here; the sub-families that ARE exactly
/// reconstructible are DERIVED as multi-step `bitblast_*` sequences by
/// `ay_proof`'s Alethe printer instead.
/// DELIBERATELY NOT ALIASED — `ite_same` → `ite_simplify`. The pair is
/// admissible on paper: `ay_proof::recognize_ite_same` admits EXACTLY the unit
/// positive equality `(= L R)` where one side is `Ite(c, t, e)` with `t == e`
/// (same `TermId`) equal to the other side, and carcara's `ite_simplify`
/// re-derives that in ONE rewrite (patterns 1–3 of its twelve-pattern set all
/// collapse an identical-branch `ite` to the branch, so the fixed-point loop
/// hits the goal immediately and cannot cycle). It is not shipped because it
/// buys nothing measurable: the only reconstruction that emits
/// [`crate::proof::TheoryLemmaKind::IteSame`] is
/// `Executor::promote_ite_same_collapse`, whose proof carcara already rejects
/// at the `assume`, not at the lemma — on `(assert (not (= (ite p a a) a)))`
/// the source-spelling override prints the value term `a` as `(ite p a a)`, so
/// the assume reaches the wire as
/// `(not (= (ite p (ite p a a) (ite p a a)) (ite p a a)))` and carcara answers
/// "could not match term to any of the original problem premises" => `invalid`
/// before and after the rename. Renaming the lemma would move an `invalid`
/// document to a different `invalid` document. Fix the assume expansion first;
/// until then the honest `hole` is the correct wire name.
///
/// # Audited and REJECTED: the strings / regex / arithmetic family
///
/// Every candidate below was run against the pinned checker as a bare
/// theory-lemma step carrying a clause its AY kind is actually allowed to
/// carry. All twelve stay honest holes; the tests in this module lock that in.
///
/// The strings and regex candidates fail for one STRUCTURAL reason, not twelve
/// separate shape mismatches: a theory lemma prints as
/// `(step id (cl …) :rule R)` with no `:premises` and no `:args` (see
/// `ay_proof::AlethePrinter::format_theory_lemma`), while *every* string and
/// regex rule the checker implements demands at least one of them —
/// `concat_eq`/`concat_conflict`/`string_decompose` (1 premise + 1 arg),
/// `concat_unify` (2 + 1), the eight `concat_*split*`/`*prop_*` rules and
/// `re_inter` (2 premises), `string_length_non_empty` and the five
/// `re_*unfold*` rules (1 premise), `string_length_pos` (1 arg). The checker
/// rejects on that count before it ever inspects the clause, so the set of AY
/// steps any of them would accept is EMPTY. Measured verdicts, e.g.
/// `re_inter` given `(cl (not (str.in_re x R₁)) (not (str.in_re x R₂)))`:
/// `expected 2 premises, got 0` → `invalid`, where `hole` gives `holey`.
///
/// The two named near-misses resolve as follows.
///
/// * `regex_intersect_empty` → `re_inter` is not a near-miss at all once read:
///   `re_inter` INTRODUCES a positive membership, deriving the unit
///   `(cl (str.in_re x (re.inter s t)))` from premises `(str.in_re x s)` and
///   `(str.in_re x t)`. AY's kind states the opposite — a premise-free
///   two-literal tautology of NEGATED memberships whose jointly denied
///   languages have empty intersection. Opposite polarity, different arity,
///   different claim: mapping it would be a false certificate, and it does not
///   even fail quietly.
/// * `lia_mod_range` → `mod_simplify`: `mod_simplify` is ground constant
///   folding — conclusion `(cl (= (mod a b) r))` with `a`, `b` integer
///   CONSTANTS and `r` the true remainder, hence always in `[0, |b|)`. AY's
///   kind carries `(cl (not (= (mod x d) r)))` over a SYMBOLIC `x` with `r`
///   deliberately OUTSIDE that range. The accepted sets are disjoint on
///   polarity, on groundness and on the range predicate; measured, the negated
///   form answers `term '(not (= (mod n 4) 7))' is of the wrong form, expected
///   '(= l r)'`, and even the positive form answers `expected term 'n' to be a
///   numerical constant`.
///
/// The remainder have no counterpart to argue about. `string_ground_eval` has
/// none because the checker's `evaluate` returns "cannot evaluate" for every
/// string and regex operator — `(cl (= (str.len "abc") 3))` is rejected — so
/// it decides no string fact at all. `nra_interval_unsat` and
/// `nra_univariate_unsat` are nonlinear: `la_generic` needs Farkas `:args`
/// over a linear conflict, and `la_tautology` given `(cl (not (< 0 (* n n))))`
/// answers `final disequality is not tautological`. The remaining seven —
/// `string_containment_identity`, `string_concat_cancellation`,
/// `string_ground_factor_conflict`, `regex_length_lower_bound`,
/// `string_length`, `string_length_lemma` and `string_code_inj` — have no rule
/// of that inference anywhere in the calculus.
const WIRE_RULE_ALIASES: [(&str, &str); 0] = [];

/// True if the Alethe checker recognizes `name`, i.e. dispatching it does not
/// fail with an unknown-rule `invalid` verdict.
///
/// The table is therefore a claim about the PINNED checker, not about Alethe in
/// general, and it is only as good as the last time someone measured it.
/// `dt_clash` was listed here until it was probed directly against the pinned
/// `carcara 1.1.0 [git master 9a352ee]`, which answered
/// `checking failed on step 't3' with rule 'dt_clash': unknown rule` and
/// returned `invalid` for the whole document — exactly the verdict this
/// predicate promises will not happen. Diffing the full table against that
/// build's dispatch names showed it was the only such entry.
///
/// Nothing emitted it, so nothing was broken; the coverage test in
/// `ay-proof/tests/wire_rule_coverage.rs` probes only names production can
/// actually reach, which is why it stayed green. But `WIRE_RULE_ALIASES`
/// already records one attempt to alias `dt_distinct` onto `dt_clash` that had
/// to be reverted for this exact reason, and leaving the name in the
/// vocabulary invites the same mistake a third time. The pinned checker
/// implements no datatype rules at all.
///
/// This is deliberately only a parser/dispatch vocabulary predicate. Some
/// recognized rules are semantic placeholders: notably `hole` and
/// `lia_generic` are accepted but leave the document holey rather than
/// checking the inference. Callers deciding proof authority must use the
/// effective wire rule selected for the complete step, not this name-only
/// predicate.
#[must_use]
pub fn is_checkable_alethe_rule(name: &str) -> bool {
    CHECKABLE_ALETHE_RULES.binary_search(&name).is_ok()
}

/// Checker-recognized rule names that do not establish their conclusion.
///
/// Keep this separate from [`CHECKABLE_ALETHE_RULES`]: the document parser
/// must continue to recognize both spellings, while production emission must
/// disclose them as the single canonical unproved rule. `lia_generic` is an
/// integer-arithmetic placeholder in the pinned checker; an actual linear
/// certificate may be promoted to `la_generic` only by the proof exporter's
/// complete-step wire decision.
const SEMANTICALLY_UNCHECKED_ALETHE_RULES: [&str; 2] = ["hole", "lia_generic"];

/// Map an internal rule name to the name that may be written into a proof.
///
/// Returns `name` unchanged when the checker implements it, its
/// `WIRE_RULE_ALIASES` spelling when the checker implements the same
/// inference under another name, and [`UNPROVED_STEP_RULE`] otherwise. Never
/// invents a rule name and never substitutes a *different* inference: claiming
/// `arrays_ext` for a step that is not an `arrays_ext` inference would fail the
/// checker just as loudly, and claiming it for one that happens to pass would
/// be a false certificate.
///
/// Wire names may never run ahead of the installed checker. The former
/// `dt_distinct` → `dt_clash` alias demonstrated why: the installed carcara
/// answered `unknown rule`, turning every affected document `invalid`, while
/// the fallback below produces the strictly better `holey` verdict. See
/// `WIRE_RULE_ALIASES` for the measured probe. This changes no native
/// soundness gate: AY still re-validates datatype distinctness from the proof
/// IR and constructor registry; only the unsupported external claim is
/// withdrawn.
#[must_use]
pub fn wire_rule_name(name: &str) -> &str {
    if SEMANTICALLY_UNCHECKED_ALETHE_RULES
        .binary_search(&name)
        .is_ok()
    {
        return UNPROVED_STEP_RULE;
    }
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
    /// Distinct elimination: `(= (distinct t1 .. tn) <pairwise-disequality expansion>)`
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

    /// Quantifier-negation De Morgan step: `¬∃x⃗.φ ≡ ∀x⃗.¬φ`.
    ///
    /// The conclusion is the two-literal clause `(cl (exists (x⃗) φ)
    /// (forall (x⃗) (not φ)))`, i.e. the tautology `(∃x⃗.φ) ∨ (∀x⃗.¬φ)`. It is
    /// valid because the second disjunct is exactly the negation of the first:
    /// `¬(∀x⃗.¬φ) = ∃x⃗.¬¬φ = ∃x⃗.φ`, so the clause is `A ∨ ¬A`. Resolving it
    /// against an assumed `(not (exists (x⃗) φ))` mints the entailed universal
    /// `(forall (x⃗) (not φ))`, which the existing `forall_inst` path then
    /// instantiates. See
    /// `ay_proof::checker::quantifier::validate_qnt_neg_exists` for the strict
    /// re-derivation and its soundness argument.
    ///
    /// Appended to preserve serialized discriminants of the older variants.
    QntNegExists,

    /// One bound of a FRESH-symbol definitional extension: `(cl (<= d lin))`
    /// or `(cl (<= lin d))`, with the defined symbol `d` in `:args`.
    ///
    /// This is NOT an inference and its clause is NOT a tautology — `d <= lin`
    /// is false for most valuations of a symbol the problem constrains. It is
    /// sound for exactly the same reason `array_ext_diff_intro` is: `d` is a
    /// symbol the PROBLEM never mentions, so any model of the problem extends
    /// to one that also satisfies the bound by taking `d := lin`, and a
    /// refutation of the extended set is therefore a refutation of the
    /// original. Adding facts about a fresh symbol is conservative; adding the
    /// same fact about a constrained symbol is not, and only a checker that
    /// verifies freshness AGAINST the problem can tell the two apart.
    ///
    /// The whole-proof conditions (one definiens per symbol, no introduced
    /// symbol inside any definiens, matching sorts, freshness against the
    /// problem and against every `assume`) are enforced once by
    /// `ay_proof`'s `FreshDefRegistry`; see its `collect` for the soundness
    /// argument and the guard-by-guard rationale. Emitted by the executor's
    /// `derive_fresh_definitional_bounds` lane in place of the premiseless
    /// `trust` these leaves used to demote to.
    ///
    /// Appended to preserve serialized discriminants of the older variants.
    FreshDefBound,

    /// A FRESH-symbol definitional EQUALITY: `(cl (= d expr))`, with the
    /// defined symbol `d` in `:args`.
    ///
    /// The sibling of [`Self::FreshDefBound`] and the more direct form of the
    /// same conservative definitional extension: where a bound asserts one
    /// HALF of `d = lin`, this asserts the definition outright, and over any
    /// sort rather than only the arithmetic one `<=` admits. Measured on this
    /// repository's corpus, the producer is `purify_bool_args`, which mints a
    /// fresh Boolean `p` for a compound Boolean argument `b` and asserts
    /// `(= p b)` so that EUF can congruence-close over `f(p)`.
    ///
    /// This is NOT an inference and its clause is NOT a tautology — `(= d
    /// expr)` is false for most valuations of a symbol the problem constrains.
    /// It is sound because `d` is a symbol the PROBLEM never mentions, so any
    /// model of the problem extends to one that also satisfies the equality by
    /// taking `d := expr`, and a refutation of the extended set is therefore a
    /// refutation of the original. Adding facts about a fresh symbol is
    /// conservative; adding the same fact about a constrained symbol is not,
    /// and only a checker that verifies freshness AGAINST the problem can tell
    /// the two apart.
    ///
    /// The whole-proof conditions (one definiens per symbol ACROSS BOTH fresh-
    /// definition rules, no introduced symbol inside any definiens, matching
    /// sorts, freshness against the problem and against every `assume`) are
    /// enforced once by `ay_proof`'s `FreshDefRegistry`; see its `collect` for
    /// the soundness argument and the guard-by-guard rationale. Sharing that
    /// ONE registry with `fresh_def_bound` is a soundness requirement, not a
    /// convenience: `(<= d 0)` from one rule and `(= d (+ x 1))` from the other
    /// are two definientia for one symbol and jointly force `x + 1 <= 0`.
    ///
    /// Appended to preserve serialized discriminants of the older variants.
    FreshDefEq,

    /// Clause PERMUTATION: the conclusion carries exactly the premise's
    /// literals, with the same multiplicities, in a different order.
    ///
    /// An Alethe clause IS a disjunction, and `or` is commutative, so a
    /// permutation of a derived clause is entailed by it — the rule adds no
    /// information and needs no theory. It exists because several of AY's own
    /// validators are ORDER-SENSITIVE (`eq_transitive` wants its positive
    /// conclusion LAST), so a producer that must record a clause in a
    /// validator's accepted order still owes its consumers the order they
    /// already reference. `reordering` is the step that reconciles the two
    /// without touching either.
    ///
    /// `reordering` is a pinned wire rule (`CHECKABLE_ALETHE_RULES`), so the
    /// printer lowers it under its own name and the external checker re-runs
    /// the same permutation check `ay_proof`'s `validate_reordering` does.
    ///
    /// Appended to preserve serialized discriminants of the older variants.
    Reordering,
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
            Self::QntNegExists => "qnt_neg_exists",
            Self::FreshDefBound => "fresh_def_bound",
            Self::FreshDefEq => "fresh_def_eq",
            Self::Reordering => "reordering",
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
mod wire_name_tests;
