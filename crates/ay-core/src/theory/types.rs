// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::proof::FarkasAnnotation;
use crate::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Native-code backend accepted for theory-bound propagation.
///
/// This deliberately names only the external code generation path. Retired external backends
/// must not satisfy this contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeTheoryPropagationBackend {
    /// external code generation native theory-bound propagation.
    ExternalCodegenBackend,
}

/// Metadata exported by a theory solver for native theory-bound propagation.
///
/// DPLL treats this as an eligibility contract, not as permission to dispatch:
/// callers must still apply their own fail-closed control plane before using a
/// native path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeTheoryPropagationProfile {
    /// The theory solver does not expose a native bound-propagation contract.
    Unsupported,
    /// Per-variable arithmetic bound propagation can be represented natively.
    BoundPropagation {
        /// Native backend used by the compiled bound propagators.
        backend: NativeTheoryPropagationBackend,
        /// Number of variables with any compiled propagation metadata.
        compiled_vars: u32,
        /// Number of variables with native executable propagators.
        native_vars: u32,
        /// Total registered bound atoms covered by the metadata.
        total_atoms: u32,
        /// Registered bound atoms that fit the small integer/rational fast path.
        small_atoms: u32,
    },
}

impl NativeTheoryPropagationProfile {
    /// Unsupported profile used by theories without native propagation metadata.
    #[must_use]
    pub fn unsupported() -> Self {
        Self::Unsupported
    }

    /// external code generation profile for arithmetic bound propagation.
    #[must_use]
    pub fn external_codegen_backend_bound_propagation(
        compiled_vars: u32,
        native_vars: u32,
        total_atoms: u32,
        small_atoms: u32,
    ) -> Self {
        Self::BoundPropagation {
            backend: NativeTheoryPropagationBackend::ExternalCodegenBackend,
            compiled_vars,
            native_vars,
            total_atoms,
            small_atoms,
        }
    }
}

/// A signed theory literal (term + Boolean value).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TheoryLit {
    /// The term representing the (Boolean) atom.
    pub term: TermId,
    /// The Boolean value of the atom.
    pub value: bool,
}

impl TheoryLit {
    /// Create a new signed theory literal.
    #[must_use]
    pub fn new(term: TermId, value: bool) -> Self {
        Self { term, value }
    }
}

/// A theory clause that should be added permanently to the SAT solver.
///
/// Unlike [`TheoryConflict`], these literals already represent the clause
/// polarity that should be asserted. For example, the ROW2 axiom
/// `i = j OR select(store(a, i, v), j) = select(a, j)` is encoded directly as
/// two positive clause literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryLemma {
    /// The literals of the clause in SAT polarity.
    pub clause: Vec<TheoryLit>,
}

impl TheoryLemma {
    /// Create a new theory lemma clause.
    #[must_use]
    pub fn new(clause: Vec<TheoryLit>) -> Self {
        Self { clause }
    }
}

/// A request from a theory solver to split on an integer variable.
///
/// Used for branch-and-bound in LIA: when the LRA relaxation gives x = 2.5,
/// the solver requests a split to force (x <= 2) OR (x >= 3).
#[derive(Debug, Clone)]
pub struct SplitRequest {
    /// The integer variable to split on
    pub variable: TermId,
    /// The non-integer value from the LRA relaxation
    pub value: BigRational,
    /// Floor of the value (lower bound in the split)
    pub floor: BigInt,
    /// Ceiling of the value (upper bound in the split)
    pub ceil: BigInt,
}

/// Request for the DPLL executor to create and assert a tighter bound atom.
///
/// Produced when implied-bound analysis derives a bound that no existing
/// unassigned Boolean atom represents. The executor creates the atom after
/// releasing the theory's immutable `TermStore` borrow, then adds the
/// implication clause `reason -> atom`.
///
/// Reference: Z3 `theory_lra::refine_bound()` in `reference/z3/src/smt/theory_lra.cpp`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRefinementRequest {
    /// Left-hand arithmetic term to refine.
    pub variable: TermId,
    /// Optional right-hand arithmetic term for relative refinements.
    ///
    /// When present, the refined atom is `variable <= rhs_term + bound_value`
    /// or `variable >= rhs_term + bound_value` depending on `is_upper`.
    /// When absent, the refinement is against a numeric constant.
    pub rhs_term: Option<TermId>,
    /// Derived bound value before Int floor/ceil canonicalization.
    pub bound_value: BigRational,
    /// `true` for an upper-bound refinement, `false` for a lower-bound refinement.
    ///
    /// With `rhs_term == None`, this is `variable <= bound_value` or
    /// `variable >= bound_value`. With `rhs_term == Some(rhs)`, it is
    /// `variable <= rhs + bound_value` or `variable >= rhs + bound_value`.
    pub is_upper: bool,
    /// Whether the variable is Int-sorted.
    pub is_integer: bool,
    /// Antecedent literals justifying the implied bound.
    pub reason: Vec<TheoryLit>,
}

/// A request from a theory solver to split on a disequality.
///
/// Used when a disequality `x != c` is violated by the current model (x = c)
/// but the variable has slack (can take other values). The DPLL(T) layer
/// should create atoms `x < c` and `x > c` and add a clause to exclude `x = c`
/// only when the disequality is active.
///
/// When `disequality_term` is Some, the clause polarity depends on `is_distinct`:
/// - For `distinct` terms (is_distinct=true): `~term OR (x < c) OR (x > c)`
///   Forces split when distinct is asserted true (disequality holds)
/// - For `=` terms (is_distinct=false): `term OR (x < c) OR (x > c)`
///   Forces split when equality is asserted false (disequality holds)
///
/// When `disequality_term` is None (legacy behavior), the clause is:
///   `(x < c) OR (x > c)` (unconditional - may cause soundness issues!)
#[derive(Debug, Clone)]
pub struct DisequalitySplitRequest {
    /// The variable/expression that must be different from the excluded value
    pub variable: TermId,
    /// The value that is excluded by the disequality
    pub excluded_value: BigRational,
    /// The original equality/distinct term that triggered the disequality.
    /// When present, this is used to make the split conditional.
    pub disequality_term: Option<TermId>,
    /// Whether the disequality_term is a `distinct` term (true) or `=` term (false).
    /// This determines the polarity of the conditional clause literal.
    pub is_distinct: bool,
}

/// A request from a theory solver to split on a multi-variable expression.
///
/// Used when a multi-variable disequality `E != F` (or `E - F != 0`) is violated.
/// Single-value enumeration doesn't work for these - we need to split on
/// `E < F OR E > F` directly. The DPLL(T) layer should parse the disequality
/// term to extract LHS and RHS, then create atoms for the comparison.
#[derive(Debug, Clone)]
pub struct ExpressionSplitRequest {
    /// The disequality term that was violated (the `distinct` or negated `=` term).
    /// The SMT layer should extract LHS and RHS from this term.
    pub disequality_term: TermId,
}

/// A request from a combined theory solver to speculatively assume a model equality.
///
/// Used for Nelson-Oppen theory combination with non-convex theories (#4906).
/// When the arithmetic model implies `lhs = rhs` (both evaluate to the same value),
/// the DPLL(T) layer should create an `(= lhs rhs)` atom, set its SAT variable's
/// phase to `true`, and continue solving. The equality becomes a normal CDCL decision
/// that is retracted on conflict — unlike `assert_shared_equality` which is permanent.
///
/// Reference: Z3 `smt_context.cpp:4576-4632` (`assume_eq` + `try_true_first`).
#[derive(Debug, Clone)]
pub struct ModelEqualityRequest {
    /// Left-hand side of the model equality.
    pub lhs: TermId,
    /// Right-hand side of the model equality.
    pub rhs: TermId,
    /// Reason literals justifying why the model implies this equality.
    /// Used for conflict analysis if the equality leads to a contradiction.
    pub reason: Vec<TheoryLit>,
    /// True when `reason` is a theory proof of `lhs = rhs`, not just model
    /// guidance. Split-loop encoders may then add `!reason \/ lhs = rhs`.
    pub implied: bool,
}

/// A lemma request from the string theory solver.
///
/// Describes a split that needs new terms created (skolems, concat applications)
/// and a disjunctive clause added to the SAT solver. The executor creates the
/// actual terms and clause because the theory solver only holds `&TermStore`
/// (immutable) and cannot create new terms.
///
/// Reference: CVC5 `core_solver.cpp:731-852` (`getConclusion`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringLemma {
    /// The kind of split lemma.
    pub kind: StringLemmaKind,
    /// First component (the term being split).
    pub x: TermId,
    /// Second component or constant (depends on kind).
    pub y: TermId,
    /// Character offset into the constant `y` (for ConstSplit with partial
    /// constant consumption). When non-zero, the executor extracts the
    /// character at position `char_offset` instead of position 0.
    /// Default: 0 (first character).
    ///
    /// For `ConstUnify`, `char_offset` is the END index of the substring of
    /// `y` that the variable `x` unifies with; the START index is
    /// `start_offset` (see below). The variable equals `y[start_offset..char_offset]`.
    pub char_offset: usize,
    /// Substring START offset into the constant `y` for `ConstUnify` lemmas.
    ///
    /// When a concat component is compared against a constant that has been
    /// partially consumed by a preceding component (e.g. `["a", y]` vs `"ab"`
    /// leaves `y` aligned at offset 1 of `"ab"`), the variable unifies with the
    /// *substring* `y[start_offset..char_offset]`, not the prefix
    /// `y[0..char_offset]`. Without this, partial-offset `ConstUnify` would
    /// assign the wrong value (e.g. `y = "ab"` instead of `y = "b"`), stalling
    /// the CEGAR loop on satisfiable concat+length instances.
    ///
    /// Only meaningful for `ConstUnify`; all other lemma kinds leave it 0.
    pub start_offset: usize,
    /// NF explanation (antecedent) for context-dependent lemmas.
    ///
    /// ConstSplit and VarSplit lemmas are NOT universally valid — they depend
    /// on the NF comparison context (which character position the variable
    /// falls at). Including the reason as negated guard literals in the clause
    /// makes the lemma universally valid: `¬(reason) ∨ conclusion`.
    ///
    /// EmptySplit and LengthSplit are universally valid and have empty reasons.
    ///
    /// Without guards, stale ConstSplit clauses persist after DPLL backtracking
    /// and force variables to wrong characters, causing false UNSAT (#4094).
    ///
    /// Reference: CVC5 `sendInference(ant, conc, ...)` where `ant` is the
    /// NF explanation.
    pub reason: Vec<TheoryLit>,
}

/// Kind of string split lemma.
///
/// Maps to CVC5's `processSimpleNEq` Cases 6-9.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StringLemmaKind {
    /// Case 6: `len(x) = len(y) OR len(x) != len(y)`.
    /// Both components are non-constant variables with unknown length relationship.
    LengthSplit,
    /// Case 8 (prerequisite): `x = "" OR x != ""`.
    /// A non-constant component might be empty; determine before const-split.
    EmptySplit,
    /// Case 8: `x = firstChar(y) ++ k` where `y` is the constant.
    /// A non-constant variable vs a string constant; peel first character.
    ConstSplit,
    /// Case 9: `(x = y ++ k) OR (y = x ++ k)`.
    /// Both non-constant, lengths disequal; variable-variable split.
    VarSplit,
    /// Positive `str.contains(x, y)` reduction: `x = sk1 ++ y ++ sk2`.
    /// When `str.contains(x, y)` is asserted true but arguments are not
    /// ground-resolvable, decompose `x` into prefix + `y` + suffix.
    /// Reference: CVC5 `extf_solver.cpp:181-202`
    ContainsPositive,
    /// On-demand `str.substr(s, n, m)` reduction.
    ///
    /// The executor lowers `x = str.substr(s, n, m)` into the same skolemized
    /// word-equation + arithmetic axiom used by eager preregistration, but
    /// only when the string core requests it at runtime. `x` is the substr
    /// application term; `y` is unused.
    SubstrReduction,
    /// On-demand `str.indexof(s, w, n)` reduction (CAP-2).
    ///
    /// The executor lowers the indexof application into the cvc5-style
    /// first-occurrence axiom:
    /// - `n < 0 ∨ n > len(s)` → result is `-1`;
    /// - `w = ""` (in range) → result is `n`;
    /// - the search window `substr(s, n, len(s)-n)` contains `w` → the window
    ///   decomposes as `pre ++ w ++ suf` with `result = n + len(pre)` and a
    ///   leftmost guard `¬contains(pre ++ w[0..len(w)-1], w)`;
    /// - otherwise the result is `-1`.
    ///
    /// `x` is the indexof application term; `y` is unused.
    IndexofReduction,
    /// On-demand `str.replace(s, t, u)` reduction (CAP-2 follow-on).
    ///
    /// First-occurrence replacement:
    /// - `t = ""` → result is `u ++ s`;
    /// - `contains(s, t)` → `s = pre ++ t ++ suf` with a leftmost guard
    ///   `¬contains(pre ++ t[0..len(t)-1], t)` and result `pre ++ u ++ suf`;
    /// - otherwise result is `s`.
    ///
    /// `x` is the replace application term; `y` is unused.
    ReplaceReduction,
    /// On-demand `str.to_int(s)` reduction via digit decomposition (extf
    /// wave 2).
    ///
    /// Requires a concrete upper bound `L` on `len(s)` derived from an
    /// asserted length literal; `char_offset` carries `L` and `reason`
    /// carries the bound literal (all emitted case clauses are guarded by
    /// its negation so DPLL backtracking of the bound deactivates them).
    ///
    /// Exact SMT-LIB semantics: the result is `-1` unless `s` is a NONEMPTY
    /// all-digit (`[0-9]`) string; leading zeros are allowed and contribute
    /// to the decimal value.
    ///
    /// `x` is the to_int application term (Int sorted); `y` is unused.
    ToIntReduction,
    /// On-demand `str.from_int(n)` reduction (extf wave 2).
    ///
    /// Universally valid (no bound needed):
    /// `ite(n >= 0, to_int(r) = n ∧ r ∈ ("0" | [1-9][0-9]*), r = "")`
    /// where `r` is the from_int application itself. The canonical-decimal
    /// regex forbids leading zeros; combined with `to_int(r) = n` this is
    /// exactly SMT-LIB `str.from_int` for `n >= 0`, and `n < 0` yields `""`.
    ///
    /// `x` is the from_int application term; `y` is unused.
    FromIntReduction,
    /// On-demand `str.replace_all(s, t, u)` one-step reduction (extf wave 2).
    ///
    /// First-match decomposition with recursion on the suffix:
    /// - `t = ""` → result is `s` UNCHANGED (differs from `str.replace`!);
    /// - `contains(s, t)` → `s = pre ++ t ++ suf` with the leftmost guard
    ///   `¬contains(pre ++ t[0..len(t)-1], t)` and result
    ///   `pre ++ u ++ replace_all(suf, t, u)` (a fresh application term that
    ///   is reduced on demand in a later CEGAR round, budget-bounded);
    /// - otherwise result is `s`.
    ///
    /// `x` is the replace_all application term; `y` is unused.
    ReplaceAllReduction,
    /// On-demand `str.replace_re(s, R, u)` partial reduction (extf wave 2).
    ///
    /// Emitted only for GROUND, engine-evaluable regexes. Encodes the valid
    /// no-match guard `s ∈ Σ*·R·Σ* ∨ r = s` (no match anywhere in `s` means
    /// the result is `s` unchanged) and marks the application reduced so it
    /// stops latching `incomplete`. The exact first-match semantics are
    /// enforced by ground evaluation once the haystack resolves (the regex
    /// engine computes the leftmost-shortest match) plus the definitive
    /// model-validation chokepoint; an unresolved membership latches the
    /// regexp solver's incompleteness, keeping Unknown honest.
    ///
    /// `x` is the replace_re application term; `y` is unused.
    ReplaceReReduction,
    /// On-demand `str.replace_re_all(s, R, u)` partial reduction (extf
    /// wave 2). Same shape and soundness argument as [`Self::ReplaceReReduction`];
    /// ground evaluation replaces every leftmost-shortest NON-EMPTY match.
    ///
    /// `x` is the replace_re_all application term; `y` is unused.
    ReplaceReAllReduction,
    /// Length-aware constant unification (#4055): `x = prefix(y, char_offset)`.
    /// When a variable `x` has a known length `n` (via N-O bridge) and is
    /// compared against a constant `y` with `len(y) >= n`, directly assert
    /// `x = y[0..n]`. The `char_offset` field carries `n` (the prefix length).
    /// This replaces character-by-character ConstSplit for the common case
    /// of dual-concat NF comparisons (e.g., prefix+suffix decompositions).
    ConstUnify,
    /// Disequality equality split: `x = y OR x != y`.
    /// Emitted by `process_simple_deq` when two NF components have equal
    /// lengths but unknown equality status. Forces the SAT solver to decide
    /// whether the components are equal (disequality may still hold via other
    /// components) or disequal (directly satisfying the disequality).
    /// Reference: CVC5 `core_solver.cpp:2280-2300` (DEQ_STRINGS_EQ).
    EqualitySplit,
    /// Disequality empty split: `x = "" OR x != ""`.
    /// Emitted by `process_deq_disl` when one NF component is constant and
    /// the other is a non-constant that may be empty. Forces the SAT solver
    /// to decide whether the non-constant is empty before decomposition.
    /// Reference: CVC5 `core_solver.cpp:2157-2167` (DEQ_DISL_EMP_SPLIT).
    DeqEmptySplit,
    /// Disequality first-char equality split: `x = c OR x != c`.
    /// Emitted when a non-constant has length 1 and the other side is a
    /// constant `c` (its first character). Splits on character equality.
    /// Reference: CVC5 `core_solver.cpp:2192-2198` (DEQ_DISL_FIRST_CHAR_EQ_SPLIT).
    DeqFirstCharEqSplit,
}

/// A theory conflict with optional Farkas coefficients.
///
/// This struct bundles the conflicting literals with their Farkas coefficients
/// for arithmetic theories (LRA/LIA). The coefficients are essential for
/// Craig interpolation in CHC solving.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TheoryConflict {
    /// The conflicting literals (bounds that cannot all hold)
    pub literals: Vec<TheoryLit>,
    /// Optional Farkas coefficients for interpolation
    /// Present when the conflict comes from LRA/LIA with proof production enabled
    pub farkas: Option<FarkasAnnotation>,
}

impl TheoryConflict {
    /// Create a conflict without Farkas coefficients
    #[must_use]
    pub fn new(literals: Vec<TheoryLit>) -> Self {
        Self {
            literals,
            farkas: None,
        }
    }

    /// Create a conflict with Farkas coefficients
    #[must_use]
    pub fn with_farkas(literals: Vec<TheoryLit>, farkas: FarkasAnnotation) -> Self {
        Self {
            literals,
            farkas: Some(farkas),
        }
    }
}

/// Result of a theory check
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum TheoryResult {
    /// The current assignment is satisfiable
    Sat,
    /// The current assignment is unsatisfiable, with a conflicting set of signed literals.
    ///
    /// The returned set represents assignments that cannot all hold simultaneously.
    /// The DPLL(T) layer negates these literals to produce a blocking clause.
    Unsat(Vec<TheoryLit>),
    /// Unknown (theory solver could not determine)
    Unknown,
    /// Theory needs to split on an integer variable for branch-and-bound.
    ///
    /// The DPLL layer should create atoms `var <= floor` and `var >= ceil`,
    /// add the clause `(var <= floor) OR (var >= ceil)`, and continue solving.
    NeedSplit(SplitRequest),
    /// Theory needs to split on a disequality.
    ///
    /// The DPLL layer should create atoms `var < value` and `var > value`,
    /// add the clause `(var < value) OR (var > value)`, and continue solving.
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs to split on a multi-variable expression disequality.
    ///
    /// Used when `E != F` is violated but single-value enumeration would be infinite.
    /// The DPLL layer should parse the disequality term to get LHS and RHS,
    /// then create atoms `LHS < RHS` and `LHS > RHS`, add the clause
    /// `(LHS < RHS) OR (LHS > RHS)`, and continue solving.
    NeedExpressionSplit(ExpressionSplitRequest),
    /// Unsatisfiable with optional Farkas coefficients for interpolation.
    ///
    /// This variant is used by arithmetic theories (LRA/LIA) when proof production
    /// is enabled. The Farkas coefficients provide a certificate of infeasibility
    /// that can be used for Craig interpolation in CHC solving.
    UnsatWithFarkas(TheoryConflict),
    /// String theory needs a split lemma added to the SAT solver.
    ///
    /// The executor creates new terms (skolems, concat applications) from the
    /// symbolic description and adds the resulting clause. The theory solver
    /// cannot create these directly because it only holds `&TermStore`.
    NeedStringLemma(StringLemma),
    /// Theory needs multiple permanent clauses injected without restarting SAT.
    ///
    /// The executor adds each clause to the current SAT state and continues
    /// propagation from the existing trail. This is used by array ROW2 batching
    /// to avoid one solver restart per discovered axiom (#6546).
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    ///
    /// The DPLL layer should create an `(= lhs rhs)` atom with a SAT variable,
    /// set its phase to `true`, and continue solving. The equality becomes a
    /// retractable CDCL decision — if it leads to conflict, the solver backtracks.
    ///
    /// Reference: Z3 `assume_eq` + `try_true_first` (smt_context.cpp:4576-4632).
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant of `NeedModelEquality`: request multiple speculative
    /// model equalities in one pipeline restart instead of one-per-restart.
    ///
    /// This avoids O(N) pipeline restarts when the N-O fixpoint discovers N
    /// unresolved index pairs simultaneously (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
    /// Batch variant of `NeedExpressionSplit`: request multiple multi-variable
    /// disequality splits in one pipeline restart instead of one-per-restart.
    ///
    /// When constraints like `(distinct E1 E2 ... En)` over arithmetic
    /// expressions violate their disequalities in the LRA relaxation, the
    /// solver previously returned the first `NeedExpressionSplit` and restarted
    /// the SAT solver. On 8-queens-style problems with 28 pairwise multi-var
    /// disequalities per `distinct`, this caused ~30 full SAT restarts per
    /// distinct constraint. Batching encodes all violated splits in a single
    /// iteration (#8707).
    NeedExpressionSplits(Vec<ExpressionSplitRequest>),
}

/// A propagated literal from a theory solver.
///
/// Supports two modes:
/// - **Eager**: `reason` is non-empty and contains the full antecedent list.
///   The DPLL layer converts these to SAT literals immediately.
/// - **Lazy** (#8467): `reason` is empty and `reason_data` is `Some(tag)`.
///   The DPLL layer stores the propagation and calls
///   `TheorySolver::explain_propagation` only when the reason is needed
///   during conflict analysis. ~90% of propagations are never explained,
///   so this eliminates the O(reason_len) allocation per propagation.
///
/// Reference: Z3's `u_dependency` in `lp/lp_bound_propagator.h`.
#[derive(Debug, Clone)]
pub struct TheoryPropagation {
    /// The propagated literal
    pub literal: TheoryLit,
    /// The reason (antecedents) for the propagation.
    /// Empty when `reason_data` is set (lazy justification mode).
    pub reason: Vec<TheoryLit>,
    /// Opaque tag for lazy justification (#8467).
    /// When set, the theory solver can reconstruct the reason on demand
    /// via `explain_propagation(literal.term, reason_data)`.
    /// Encoding is theory-specific (e.g., LRA packs var/bound_type into u64).
    pub reason_data: Option<u64>,
}

impl TheoryPropagation {
    /// Create an eager propagation with a fully materialized reason.
    pub fn eager(literal: TheoryLit, reason: Vec<TheoryLit>) -> Self {
        Self {
            literal,
            reason,
            reason_data: None,
        }
    }

    /// Create a lazy propagation with a compact reason tag (#8467).
    /// The reason will be materialized on demand via `explain_propagation`.
    pub fn lazy(literal: TheoryLit, reason_data: u64) -> Self {
        Self {
            literal,
            reason: Vec::new(),
            reason_data: Some(reason_data),
        }
    }

    /// Whether this propagation uses lazy justification.
    pub fn is_lazy(&self) -> bool {
        self.reason_data.is_some()
    }
}

/// An equality discovered by a theory solver during Nelson-Oppen combination.
///
/// When a theory determines that two terms must be equal (e.g., LIA determines
/// that `x = 5` and `y = 5`, so `x = y`), it reports this equality for propagation
/// to other theories.
#[derive(Debug, Clone)]
pub struct DiscoveredEquality {
    /// Left-hand side of the equality
    pub lhs: TermId,
    /// Right-hand side of the equality
    pub rhs: TermId,
    /// The reason (antecedent literals) that justify this equality
    pub reason: Vec<TheoryLit>,
}

impl DiscoveredEquality {
    /// Create a new discovered equality with a reason.
    #[must_use]
    pub fn new(lhs: TermId, rhs: TermId, reason: Vec<TheoryLit>) -> Self {
        Self { lhs, rhs, reason }
    }
}

/// A disequality discovered by a theory solver during Nelson-Oppen combination.
///
/// When a theory determines that two terms must be disequal (e.g., EUF knows
/// `a != b` and shared terms `c`, `d` are in the respective equivalence
/// classes), it reports this disequality for propagation to other theories.
///
/// Reference: Z3's `propagate_th_diseqs` in `smt_context.cpp:1678-1690`.
#[derive(Debug, Clone)]
pub struct DiscoveredDisequality {
    /// Left-hand side of the disequality.
    pub lhs: TermId,
    /// Right-hand side of the disequality.
    pub rhs: TermId,
    /// The reason (antecedent literals) that justify `lhs != rhs`.
    pub reason: Vec<TheoryLit>,
}

impl DiscoveredDisequality {
    /// Create a new discovered disequality with a reason.
    #[must_use]
    pub fn new(lhs: TermId, rhs: TermId, reason: Vec<TheoryLit>) -> Self {
        Self { lhs, rhs, reason }
    }
}

/// Result of equality propagation for Nelson-Oppen theory combination.
///
/// Includes both equalities and disequalities discovered by a theory.
/// Reference: Z3's `propagate_th_eqs` + `propagate_th_diseqs` in
/// `smt_context.cpp`.
#[derive(Debug, Clone, Default)]
pub struct EqualityPropagationResult {
    /// Equalities discovered by this theory (e.g., x = y from LIA bounds)
    pub equalities: Vec<DiscoveredEquality>,
    /// Disequalities discovered by this theory (e.g., EUF congruence implies c != d)
    pub disequalities: Vec<DiscoveredDisequality>,
    /// A conflict discovered during equality propagation
    pub conflict: Option<Vec<TheoryLit>>,
}
