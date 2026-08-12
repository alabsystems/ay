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
use serde::{Deserialize, Serialize};

mod accessors;
mod annotations;
mod fp;
mod theory_lemma_kind;

pub use annotations::{BvGateType, CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation};
pub use fp::FpOp;

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

    /// Bounded mixed Bool/Int/BV semantic tautology.
    ///
    /// Every clause literal must be the explicit negation of one source-level
    /// root.  The strict checker reconstructs that conjunction and independently
    /// proves it UNSAT with the bounded BV/LIA interpreter; the producer's tag
    /// carries no authority.  This closes proof-presentation gaps for exact
    /// `bv2nat` obligations while remaining fail-closed outside the checker's
    /// finite fragment.
    ///
    /// The pinned external Alethe checker does not parse SMT-LIB `bv2nat`, so
    /// this internal certificate renders as an honest `hole` on that wire.
    BvLiaTautology,

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

    /// The definitional set-cardinality recurrence over a store chain rooted
    /// at the SYNTACTIC empty set -- the elaborated form of
    /// `set.singleton` / `set.insert` / `set.remove`.
    ///
    /// ```text
    /// (= (set.card R) 0)                                   R syntactically empty
    /// (= (set.card (store B e true))  (+ (set.card B) 1))  e not in B
    /// (= (set.card (store B e true))  (set.card B))        e in B
    /// (= (set.card (store B e false)) (set.card B))        e not in B
    /// (= (set.card (store B e false)) (- (set.card B) 1))  e in B
    /// ```
    ///
    /// THE EMPTY ROOT IS LOAD-BEARING, not incidental. A finite chain of writes
    /// over the empty carrier denotes a FINITE set, and the recurrence is a
    /// theorem of finite set theory. Over an unrestricted base it is not safe
    /// to hand out: under the interpretation `card(X) = |X|` for finite `X` and
    /// `card(X) = N` for infinite `X` (`N` above every literal-membership count
    /// in the problem) -- which satisfies [`Self::SetCardNonNegative`],
    /// [`Self::SetCardMemberLowerBound`], [`Self::SetCardEmpty`] and the
    /// finite-chain recurrence alike -- an increment over the universal set
    /// reads `N = N + 1`. Requiring the empty root keeps every instance inside
    /// the fragment where the equations are simply true. AY's own producer
    /// imposes the identical restriction (`is_covered_store_chain`).
    ///
    /// AY's strict checker establishes the empty root with a walk of its OWN,
    /// separate from the one that decides the membership side condition: the
    /// membership walk stops at the first write on the probed index and can
    /// answer without ever reaching the root, so it cannot be what confines the
    /// schema to the finite fragment.
    ///
    /// The membership side condition is likewise re-derived rather than taken
    /// on the producer's word. That walk steps past a write only when the two
    /// indices are syntactically identical or DISTINCT LITERAL constants. Two
    /// symbolic indices may denote the same element, so an undecidable chain is
    /// rejected fail-closed rather than guessed -- the difference between
    /// refusing to certify `|{x, y}| = 2` and asserting it (false when
    /// `x = y`).
    ///
    /// Either orientation of the equality is accepted; `=` is symmetric, so
    /// the two spellings are the same claim.
    ///
    /// Checkable only by AY's native strict checker; the pinned external
    /// Alethe checker has no rule for the non-standard `set.card` operator.
    SetCardChainRecurrence,

    /// Reflexivity of a collection subset predicate: `(cl (X.subset a a))` for
    /// `X` one of `set`, `map`, `multiset`.
    ///
    /// `a subset a` holds in every model of all three theories with NO side
    /// condition, which is what makes it checkable with no problem context --
    /// the same status as [`Self::SetCardNonNegative`]. All three native
    /// solvers document the same fact (`ay-set`, `ay-map`, `ay-multiset`:
    /// "reflexivity is valid ... `subset(m, m)` is a tautology"). The two
    /// operands must be the SAME term: a subset claim between different
    /// collections is not a tautology and is rejected fail-closed.
    ///
    /// These three predicates are *declaration-activated* in `ay-frontend`
    /// (user-declarable, but only at the native
    /// `(Array ..) (Array ..) -> Bool` signature, which is documented to
    /// request the native semantics). AY's strict checker does not rely on
    /// that gate: `validate_subset_reflexive` re-derives the native signature
    /// from the clause itself.
    ///
    /// Checkable only by AY's native strict checker; the pinned external
    /// Alethe checker has no rule for these AY-extension predicates, so this
    /// internal certificate renders as an honest `hole` on that wire.
    SubsetReflexive,

    /// The subset DEFINITION instantiated at one element term -- the ground
    /// witness obligation the native set/multiset solvers refute against.
    ///
    /// ```text
    /// (cl (not (set.subset A B)) (not (select A E)) (select B E))
    /// (cl (not (multiset.subset A B)) (<= (select A E) (select B E)))
    /// ```
    ///
    /// The first is `A subset B -> (E in A -> E in B)` over the
    /// `Array(I -> Bool)` membership carrier; the second is
    /// `A subset B -> count(A,E) <= count(B,E)` over the `Array(I -> Int)`
    /// multiplicity carrier. Both are entailed by the subset atom alone, so
    /// each clause is valid under every interpretation.
    ///
    /// `A`, `B` and `E` must be identical throughout -- that identity is the
    /// whole content of the axiom, and dropping it would licence
    /// `A subset B => e in C` for an unrelated `C`. The multiset `<=`
    /// orientation is likewise fixed: the mirror image is the converse claim
    /// and is false.
    ///
    /// `map.subset` is NOT covered: its element-wise definition is a
    /// conjunction over the `map.dom` projection, not this single implication,
    /// so a `map.subset` clause fails closed here.
    SubsetElementInstance,

    /// TRANSITIVITY of one collection subset predicate.
    ///
    /// ```text
    /// (cl (not (X.subset A B)) (not (X.subset B C)) (X.subset A C))
    /// ```
    ///
    /// All three native predicates order their carriers pointwise -- `set` by
    /// Boolean implication, `multiset` by `<=` on multiplicities, `map` by
    /// domain containment plus value agreement on the contained keys -- and
    /// every pointwise order is transitive, so the clause is valid under every
    /// interpretation with no side condition at all.
    ///
    /// The MIDDLE term must be shared: the second premise's subset operand
    /// must be the first premise's superset operand, and the conclusion must
    /// join the two free ends. `validate_subset_transitive` re-derives that
    /// chain from the clause alone, so a triple that does not actually connect
    /// -- which would licence an arbitrary subset claim -- is rejected
    /// fail-closed. All three atoms must use the SAME operator at one common
    /// array sort.
    ///
    /// Checkable only by AY's native strict checker; renders as an honest
    /// `hole` on the external Alethe wire, exactly like the two kinds above.
    SubsetTransitive,

    /// One collection subset atom DECIDED EXACTLY on ground carriers, under
    /// the ground bindings the clause itself carries.
    ///
    /// ```text
    /// (cl (not (= s Sg)) (not (= t Tg)) (X.subset s t))
    /// (cl (not (= s Sg)) (not (= t Tg)) (not (X.subset s t)))
    /// ```
    ///
    /// A binding literal `(not (= v g))` with `g` a GROUND carrier licenses
    /// substituting `v := g` in the conclusion: any valuation falsifying the
    /// clause makes that equality TRUE, so congruence preserves the
    /// conclusion's value under the replacement, and the substituted clause is
    /// falsifiable exactly when the original is. (The same clause-carried
    /// binding argument [`Self::FpGroundEval`] uses.)
    ///
    /// A ground carrier is `((as const (Array I E)) d)` under a bounded,
    /// cycle-free chain of `store`s at CONSTANT indices with CONSTANT values --
    /// the exact shape `(as set.empty ..)` and `set.singleton`/`set.insert`
    /// elaborate to. `validate_subset_ground_eval` decodes both operands into
    /// that normal form and decides `A subset B` POINTWISE and exactly; a
    /// negative conclusion additionally requires an explicit witness index at
    /// which the containment fails.
    ///
    /// An operand may stay UNBOUND only where the decision is universally
    /// valid without it: a positive claim whose subset operand is everywhere
    /// the carrier's bottom element holds for every superset. Everything else
    /// -- a non-ground binding, an unrecognized carrier, an unbound operand
    /// the decision needs, a mismatched polarity, any extra literal -- fails
    /// closed.
    ///
    /// Checkable only by AY's native strict checker; renders as an honest
    /// `hole` on the external Alethe wire.
    SubsetGroundEval,

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

    /// Universally-valid containment/order identity over a SYMBOLIC subject:
    /// the clause carries one of
    ///
    /// ```text
    /// (str.contains t t)   (str.prefixof t t)   (str.suffixof t t)
    /// (str.<= t t)         (not (str.< t t))
    /// (str.contains t "")  (str.prefixof "" t)  (str.suffixof "" t)
    /// ```
    ///
    /// A word contains, prefixes, suffixes and `str.<=`-precedes ITSELF, is
    /// never strictly less than itself, and contains/starts with/ends with the
    /// empty word. Each holds under EVERY interpretation, so the clause is a
    /// tautology.
    ///
    /// The two argument positions must hold the SAME `TermId` (or the exact
    /// empty-string constant in the operator's own contained-word position) —
    /// that identity IS the theorem. Two syntactically different terms may
    /// denote different words, and `str.contains` takes the CONTAINER first
    /// while `str.prefixof`/`str.suffixof` take the CONTAINED word first, so
    /// the positions are not interchangeable.
    ///
    /// This is the SYMBOLIC counterpart of [`Self::StringGroundEval`], which
    /// only decides facts whose subject is a constant. Uses AY's
    /// `string_containment_identity` rule; validated by `ay-proof` with a
    /// purely structural re-derivation that fails closed on any near-miss (two
    /// different subjects, the wrong empty-word position, a flipped polarity,
    /// non-String arguments). The pinned external Alethe checker has no rule
    /// for it, so it renders as an honest `hole` on that wire.
    StringContainmentIdentity,

    /// Free-monoid cancellation for `str.++`:
    ///
    /// ```text
    /// (cl (not (= (str.++ P… W…) (str.++ Q… W…))) (= P… Q…))   ; right
    /// (cl (not (= (str.++ W… P…) (str.++ W… Q…))) (= P… Q…))   ; left
    /// ```
    ///
    /// `str.++` denotes concatenation in the FREE monoid over the SMT-LIB
    /// alphabet, in which every element cancels on both sides: `u·w = v·w`
    /// forces `u = v`, and `w·u = w·v` forces `u = v`. Both hold under every
    /// interpretation, so the two-literal clause is a tautology.
    ///
    /// The cancelled block `W…` must be a NON-EMPTY, syntactically identical
    /// operand run at the SAME end of both sides, and each residual run must
    /// denote exactly its side of the conclusion (an empty residual is the
    /// `""` constant, a one-operand residual is that operand, a longer one is
    /// the `str.++` of exactly that run). Anything else is rejected rather
    /// than re-associated, so a producer cannot smuggle a conclusion past the
    /// residual it is supposed to name.
    ///
    /// Uses AY's `string_concat_cancellation` rule; validated by `ay-proof`
    /// with a structural re-derivation, fail-closed. The pinned external
    /// Alethe checker has no rule for it, so it renders as an honest `hole`.
    StringConcatCancellation,

    /// A containment predicate refuted by the GROUND blocks it names, over an
    /// otherwise symbolic word:
    ///
    /// ```text
    /// (cl (not (str.contains  C  (str.++ … k …))))   ; k not a factor of C
    /// (cl (not (str.prefixof  K  (str.++ m …))))     ; |K| <= |m|, K not a prefix of m
    /// (cl (not (str.suffixof  K  (str.++ … m))))     ; |K| <= |m|, K not a suffix of m
    /// ```
    ///
    /// `str.contains C T` says T's value is a CONTIGUOUS factor of C's, and a
    /// factor of a factor is a factor — so every concat block of T is a factor
    /// of C. A ground block absent from a ground container therefore refutes
    /// the containment for EVERY value of the symbolic blocks. The
    /// prefix/suffix forms pin the ground pattern against the container's
    /// ground boundary block: when the pattern is no LONGER than that block it
    /// must be its prefix/suffix, so a disagreement refutes the predicate
    /// outright. A pattern that reaches past the ground block decides nothing
    /// and is rejected.
    ///
    /// Every argument is about the ground data the clause itself carries; the
    /// symbolic blocks are never reasoned about. Uses AY's
    /// `string_ground_factor_conflict` rule; validated by `ay-proof` with an
    /// independent factor scan, fail-closed on a symbolic container, a
    /// symbolic boundary block, an empty or present factor, an over-long
    /// pattern, or a positive-polarity literal. The pinned external Alethe
    /// checker has no rule for it, so it renders as an honest `hole`.
    StringGroundFactorConflict,

    /// A regex membership bounding `str.len` BELOW:
    ///
    /// ```text
    /// (cl (not (str.in_re x R)) (<= k (str.len x)))
    /// ```
    ///
    /// where `R` is GROUND and `k` is at most the minimum word length of
    /// `L(R)`. Either `x` is outside the language and the first literal holds,
    /// or it is inside and the second does, so the clause is a tautology.
    ///
    /// This is what lets a length-arithmetic refutation use a regex the way
    /// the solver does: `x·x = "aaaa"` pins `2·len(x) = 4`, and
    /// `x ∈ ((_ re.loop 3 5) (str.to_re "a"))` pins `len(x) >= 3`, which is a
    /// plain linear contradiction once the bound is stated as a checkable
    /// clause.
    ///
    /// Validated by `ay-proof` with its OWN compositional minimum-length
    /// computation over the regex tree (`re.++` sums, `re.union` takes the
    /// smallest branch, `re.inter` the largest, `re.*`/`re.opt` give `0`,
    /// `(_ re.loop lo hi)` gives `lo` times the body). `re.comp` and every
    /// unmodelled operator REJECT rather than guess, and a non-ground leaf, a
    /// mismatched membership subject, a negative or over-strong bound, and a
    /// wrong clause shape all fail closed. Alethe has no rule for it, so it
    /// renders as an honest `hole` on that wire.
    RegexLengthLowerBound,

    /// Datatype constructor distinctness: `(cl (not (= t C1)) (not (= t C2)))`
    /// where `C1` and `C2` are applications of DISTINCT constructors of the same
    /// datatype — a value cannot equal two different constructors. Uses Alethe
    /// rule `dt_distinct`; validated by `ay-proof` against the datatype
    /// constructor registry (the proof-checker must be given the datatype
    /// declarations; without them this kind fails closed in strict mode).
    DatatypeDistinct,

    /// Finite-enum pigeonhole: `(cl (= t1 t2) (= t1 t3) ... (= t_{m-1} t_m))`,
    /// the COMPLETE graph of equalities over `m` distinct terms of a datatype
    /// sort whose `k` constructors are ALL NULLARY, with `m > k`.
    ///
    /// Such a sort's carrier is exactly its `k` constructor constants, so any
    /// `m > k` terms of it must contain an equal pair — the disjunction holds in
    /// every model. AY's native checker names this rule
    /// `dt_enum_pigeonhole`; the pinned external Alethe calculus has no
    /// datatype-exhaustiveness rule, so its diagnostic rendering remains an
    /// honest `hole` rather than emitting an unknown rule name.
    ///
    /// WHY THIS EXISTS: `add_finite_enum_pigeonhole_conflict` refutes an instance
    /// by finding a `k+1` clique in the disequality graph, then discarded the
    /// clique and pushed bare `false` as a `Generic` lemma. `[false]` is not a
    /// tautology and carries no argument, so strict mode had to reject it and
    /// every discharge lane failed — correct refutations of the QF_DT Bouvier
    /// `vlsat3` family published as `unknown`. This kind carries the argument the
    /// solver actually used.
    ///
    /// Validated by `ay-proof` against the datatype registry, which supplies both
    /// the constructor count and the nullarity that makes the carrier finite;
    /// without those declarations this kind fails closed in strict mode.
    DatatypeEnumPigeonhole,

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

    /// Floating-point clause proved valid by EXACT IEEE-754 evaluation.
    ///
    /// The claim: after substituting the bindings the clause itself carries —
    /// each negated equality `(not (= v g))` whose `v` is a variable and whose
    /// `g` is a ground term licenses replacing `v` by `g` in every literal, by
    /// congruence — the clause is TRUE under EVERY assignment of whatever
    /// variables remain, and those remaining variables span a domain the
    /// checker enumerates exhaustively within a fixed bit budget.
    ///
    /// This is the FP counterpart of [`Self::StringGroundEval`], and unlike
    /// [`Self::FpClassification`] it is not restricted to sign/class/comparison
    /// identities: `ay-proof` carries its own exact-rational IEEE-754 kernel
    /// (`fp.add`/`sub`/`mul`/`div`/`fma`/`sqrt`, all five rounding modes, and
    /// the `to_fp` / `to_fp_unsigned` conversions from bitvector bit patterns,
    /// signed/unsigned bitvector integers, reals, and other FP formats), so a
    /// refutation like `(cl (fp.eq (fp.add RNE +zero +zero) +zero))` is
    /// re-decided rather than trusted.
    ///
    /// SOUNDNESS IS RE-DERIVED, NOT LABELLED. The validator evaluates the
    /// clause itself; the producer's kind annotation carries no authority. Any
    /// operator the kernel does not implement, any variable it cannot
    /// enumerate inside the budget, any non-Boolean literal, and any
    /// assignment falsifying the clause all fail closed (reject).
    ///
    /// Alethe has no rule for exact FP evaluation, so this internal
    /// certificate renders as an honest `hole` on that wire.
    FpGroundEval,
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
    alethe_rule_requires_premises_or_args, is_checkable_alethe_rule, wire_rule_name, AletheRule,
    CHECKABLE_ALETHE_RULES, UNPROVED_STEP_RULE,
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
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "proof_tests.rs"]
mod tests;
