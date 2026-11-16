// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe proof format printer.
//!
//! Formats proof steps, clauses, terms, and constants as SMT-LIB/Alethe text.

mod aci_simp_step;
mod arith_disequality_split;
mod authored_assume;
#[cfg(test)]
#[path = "alethe_printer_authored_assume_tests.rs"]
mod authored_assume_tests;
mod bv_mul_zero;
mod bv_packed;
mod bv_shared_endpoint;
mod bv_support_memo;
pub use bv_support_memo::{
    checked_bv_bitblast_lowering_supported_within_solve,
    theory_lemma_bv_arithmetic_lowering_supported_within_solve, BvSupportDeclines,
};
mod bv_ult_zero;
mod clean_bitvec_rules;
mod closed_guard;
mod complete_blast;
mod confined_forall_instance;
mod constant_skolem_bridge;
#[cfg(test)]
#[path = "alethe_printer_disequality_split_tests.rs"]
mod disequality_split_tests;
mod dt_project;
pub use dt_project::dt_project_lowering_supported;
mod emission_progress;
#[path = "alethe_printer_eq_congruent.rs"]
mod eq_congruent;
#[path = "alethe_printer_eq_congruent_pred.rs"]
mod eq_congruent_pred;
#[path = "alethe_printer_eq_transitive.rs"]
mod eq_transitive;
pub use eq_transitive::arith_equality_chain_lowering_supported;
mod eq_transitive_support;
pub use eq_transitive_support::checked_euf_transitive_lowering_supported;
mod equality_lattice;
mod evaluate_literal;
pub use equality_lattice::lia_lattice_lowering_supported;
mod folded_assume;
mod folded_bool_closing;
#[cfg(test)]
#[path = "alethe_printer_ground_eval_tests.rs"]
mod ground_eval_tests;
mod ground_substitution;
pub use ground_substitution::checked_ground_substitution_lowering_supported;
mod ite_branch_projection;
pub use ite_branch_projection::checked_ite_branch_projection_lowering_supported;
mod guarded_row_expansion;
pub use guarded_row_expansion::checked_guarded_row_expansion_lowering_supported;
#[path = "alethe_printer_la_generic_surface.rs"]
mod la_generic_surface;
mod let_assume_confinement;
mod let_substitution;
mod mul_overflow_cert;
mod negated_exists;
mod urem_bound;
pub use mul_overflow_cert::{
    mul_overflow_division_lowering_supported, recognize_mul_overflow_division,
};
pub use urem_bound::checked_urem_bound_lowering_supported;
mod wire_rule;
use wire_rule::CheckableRule;
#[cfg(test)]
#[path = "alethe_printer_negation_shell_assume_tests.rs"]
mod negation_shell_assume_tests;
mod nra_sos;
mod offset_bridge;
pub use nra_sos::nra_sos_lowering_supported;
mod declaration_surface;
pub(crate) mod dialect;
mod permuted_or_pos;
mod printed_command;
pub use declaration_surface::carcara_declaration_gap;
mod linear_respelling;
mod negative_value_evaluate;
mod printed_la_disequality;
mod printed_operand_order;
mod printed_or;
mod printed_resolution;
mod printed_simplify;
mod printed_validity;
mod promoted_lia;
#[path = "alethe_printer_quantifier_surface.rs"]
mod quantifier_surface;
pub(crate) mod refused_surface_hole;
mod reordered_row_store;
#[path = "alethe_printer_resolution_args.rs"]
mod resolution_args;
#[cfg(test)]
#[path = "alethe_printer_row_surface_spelling_tests.rs"]
mod row_surface_spelling_tests;
mod shadowed_stores;
pub use shadowed_stores::checked_shadowed_stores_lowering_supported;
mod array_read_support;
mod respelled_atom;
mod row_prefixes;
#[cfg(test)]
mod shared_endpoint_surface_tests;
#[cfg(test)]
#[path = "alethe_printer_skolem_skeleton_tests.rs"]
mod skolem_skeleton_tests;
#[path = "alethe_printer/store_permutation.rs"]
mod store_permutation;
mod surface_and_pos;
mod surface_array_index;
pub use array_read_support::checked_array_read_lowering_supported;
mod surface_chain_equiv;
mod surface_closed_boolean;
mod surface_congruence;
mod surface_equivalence;
mod surface_implies_decomposition;
mod surface_implies_pos;
mod surface_literal;
mod surface_resolution;
mod surface_symm;
mod surface_tokens;
mod term_format;
#[cfg(test)]
#[path = "alethe_printer_wire_regression_tests.rs"]
mod wire_regression_tests;
pub use authored_assume::negation_shell_assume_surface_pairs;
pub use complete_blast::CompleteBlastAsk;
pub(crate) use surface_tokens::split_smt_term_slices_bounded;

/// An already-printed `assume` that carries one exact equality; see
/// `AlethePrinter::printed_assume_equality`.
struct PrintedAssumeEquality {
    /// The plain `assume` command.
    assume: ProofId,
    /// The carried equality is `(= right left)` rather than `(= left right)`.
    reversed: bool,
    /// `None` when the equality is the whole assumed term; otherwise how it
    /// is projected off the assumed flat conjunction.
    conjunct: Option<AssumedConjunctEquality>,
}

/// How an equality is carried by a flat assumed conjunction.
struct AssumedConjunctEquality {
    /// The printed `(not <assumed and>)` gate.
    gate: String,
    /// Where in the conjunction the equality lives.
    kind: AssumedConjunctKind,
}

enum AssumedConjunctKind {
    /// The equality is the top-level operand at this index.
    Direct(usize),
    /// The operand at `implication` is `(=> P E)` for the equality `E`, and
    /// the operand at `antecedent` is exactly `P`.
    Implied {
        implication: usize,
        implication_text: String,
        antecedent: usize,
        antecedent_text: String,
    },
}
pub(crate) use surface_literal::clause_surface_agreement;
use surface_tokens::split_smt_terms;
pub use surface_tokens::{split_alethe_application_bounded, AletheSurfaceParseError};
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    quote_symbol, string_literal, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData,
    TermId, TermStore,
};
use num_bigint::Sign;
use thiserror::Error;

/// Errors that can arise while rendering a proof to Alethe text.
///
/// Emission errors are not silent downgrades: a step that cannot be
/// rendered as a verifiable Alethe rule must bubble up so the caller can
/// refuse to produce an unverifiable proof document. See issue #8821 —
/// prior to this error, missing Farkas annotations were silently rewritten
/// to `:rule trust`, which the #8759 detector did not recognize (because
/// the underlying `ProofStep::TheoryLemma.kind` was still `LraFarkas` /
/// `LiaGeneric`, not `Generic`).
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AlethePrintError {
    /// A load-bearing `assume` is not one of the problem-scope premises passed
    /// to the exporter. Preprocessing results must be derived, never silently
    /// promoted to authored input.
    #[error(
        "reachable assume {id} uses non-problem term {term}; preprocessing-derived formulas are not proof authority"
    )]
    NonProblemAssume {
        /// Proof step containing the unauthorized assumption.
        id: ProofId,
        /// Assumed term absent from the problem scope.
        term: TermId,
    },
    /// A flat certified Skolem step could not be expanded to Carcara's scoped
    /// `anchor` + `refl` + `sko_forall` form.
    #[error("invalid certified sko_forall step {id}: {reason}")]
    InvalidSkolemStep {
        /// Identifier of the malformed step.
        id: ProofId,
        /// Exact fail-closed structural reason.
        reason: String,
    },
    /// A checked internal ROW lemma has no sound translation to the supported
    /// external array-rule shape.
    #[error("invalid array proof step {id}: {reason}")]
    InvalidArrayStep {
        /// Identifier of the unsupported or malformed ROW step.
        id: ProofId,
        /// Exact fail-closed reason.
        reason: String,
    },
    /// Surface rewriting changed a congruence step into a shape the external
    /// checker cannot justify, and no exact certified bridge applied.
    #[error("invalid surface congruence step {id}: {reason}")]
    InvalidCongruenceStep {
        /// Identifier of the malformed step.
        id: ProofId,
        /// Exact fail-closed reason.
        reason: String,
    },
    /// Surface syntax changed a checked internal rule into an external
    /// resolution/tautology whose pivot or connective no longer matches.
    #[error("invalid surface proof step {id}: {reason}")]
    InvalidSurfaceStep {
        /// Identifier of the malformed step.
        id: ProofId,
        /// Exact fail-closed reason.
        reason: String,
    },
    /// The solver retained an internally checked proof, but the external
    /// presentation authority for that exact proof is absent or stale.
    #[error("proof has no current authenticated external surface: {reason}")]
    UnavailableAuthenticatedSurface {
        /// Stable fail-closed reason supplied by the sealed producer.
        reason: &'static str,
    },
    /// An `la_generic` / `lia_generic` step is missing its Farkas coefficient
    /// annotation. Carcara rejects these rules without `:args`, and the
    /// printer will not silently fall back to `:rule trust`.
    #[error(
        "missing FarkasAnnotation for {theory} theory lemma at step-index {step} \
         (kind {kind}); cannot emit verifiable rule {rule} \
         — upstream proof tracker must attach coefficients"
    )]
    MissingFarkasAnnotation {
        /// Theory that produced the lemma (e.g., "LRA", "LIA").
        theory: String,
        /// Alethe rule name that would have been emitted.
        rule: &'static str,
        /// Debug name of the `TheoryLemmaKind` variant.
        kind: &'static str,
        /// 0-based index of the offending step in the proof.
        step: u32,
    },
    /// This array-extensionality certificate is outside the subset that can be
    /// lowered to Carcara's `arrays_ext`.
    ///
    /// `arrays_ext` requires a disequality premise and a unit conclusion whose
    /// index is the rule's exact `choice` term. AY stores a two-literal
    /// conservative-extension clause over a separately declared fresh witness,
    /// which the printer rewrites into that `choice` term at every occurrence —
    /// but only for the exactly-recognized ONE-LEVEL shape whose witness could
    /// be substituted consistently. Multi-level Skolem chains, the datatype
    /// lane's folded reads, a witness bound to two different array pairs, and
    /// an array mentioning a symbol the `choice` binder would capture all land
    /// here. Emitting `:rule extensionality` (or merely renaming it to
    /// `arrays_ext`) would be unverifiable, so the export refuses instead.
    #[error(
        "array extensionality lemma {id} has no verifiable Alethe/Carcara translation; \
         refusing to emit the unsupported `extensionality` rule"
    )]
    UnsupportedArrayExtensionality {
        /// Identifier of the theory-lemma step that cannot be rendered.
        id: ProofId,
    },
    /// The synthesized-default emission work budget was exhausted (#A2b).
    ///
    /// The by-default `<input>.alethe` certificate is best-effort: rendering
    /// must never turn a seconds-fast UNSAT verdict into minutes of proof
    /// materialization (QF_ALIA `pp-*`: 2s solves whose surface-tautology
    /// re-derivation over megabyte printed source terms ground for 300s+
    /// without completing). On exhaustion the caller keeps its verdict and
    /// prints the existing "no proof certificate emitted" degrade. Explicit
    /// `--proof` / `--strict-proofs` / `--self-check` / `:produce-proofs`
    /// exports are never budgeted.
    #[error(
        "synthesized-default proof emission work budget exhausted after {steps_rendered} steps \
         (budget {budget} work units); verdict is unaffected"
    )]
    EmissionBudgetExhausted {
        /// The configured work budget (abstract units, roughly bytes touched).
        budget: u64,
        /// Number of proof steps fully rendered before exhaustion.
        steps_rendered: u32,
    },
    /// The caller stopped this planning/emission attempt. No completed proof
    /// document is returned; the callback supplies no proof authority.
    #[error("proof emission stopped by its caller after {steps_rendered} rendered steps")]
    EmissionStopped {
        /// Number of proof steps completely rendered before refusal.
        steps_rendered: u32,
    },
    /// A `ProofStep` variant this printer has no Alethe rendering for.
    ///
    /// `ProofStep` is `#[non_exhaustive]`, so a variant added in `ay-core`
    /// reaches the printer's compiler-forced wildcard arm at runtime. Failing
    /// with a typed error (instead of panicking) lets the caller refuse to
    /// emit an unverifiable document while keeping its verdict.
    #[error("proof step {id} uses a ProofStep variant with no Alethe rendering")]
    UnsupportedStep {
        /// Identifier of the step that cannot be rendered.
        id: ProofId,
    },
    /// One surface symbol occurs at two different sorts (#A9).
    ///
    /// Ad-hoc overloading is legal SMT-LIB 2.6 (§4.2.3 reuses constructor
    /// names across independent datatypes; §3.6.4 `(as f σ)` disambiguates
    /// them) and AY solves such scripts correctly. The Alethe preamble is a
    /// flat `(declare-fun <name> () <sort>)` namespace with no overload
    /// resolution, so no faithful declaration exists: the exporter declines
    /// and the caller keeps its verdict. Formerly a `debug_assert_eq!` that
    /// aborted the process with exit 101 after `unsat` had been printed.
    #[error(
        "symbol {name} occurs at two sorts ({first} and {second}); \
         Alethe declarations are not overloaded, so no faithful preamble exists"
    )]
    AmbiguousSymbolSort {
        /// The overloaded surface symbol.
        name: String,
        /// Sort of the first occurrence encountered.
        first: Sort,
        /// Conflicting sort of a later occurrence.
        second: Sort,
    },
    /// The proof is free in symbols the problem does not declare, and an
    /// Alethe PROOF document has no command that can introduce them.
    ///
    /// AY used to open such a document with a `(declare-fun <name> () <sort>)`
    /// preamble. MEASURED against carcara 1.1.0: its Alethe proof parser
    /// accepts **no** declaration command at any position — at line 0 and
    /// mid-file alike, both abort with
    /// `parser error: unexpected token: 'declare-fun'` before a single rule is
    /// checked. So every document AY emitted with a non-empty preamble was
    /// uncheckable by construction.
    ///
    /// The one binder carcara does accept in a proof file is `define-fun`, and
    /// it is not a general substitute: it is a MACRO whose body is expanded
    /// inline, so it can only introduce a symbol whose DEFINING TERM AY
    /// actually knows. For a Skolem constant that term is the Hilbert choice
    /// `εx. B`, recorded at the mint site
    /// ([`ay_core::SkolemChoice`]) and emitted by
    /// `AlethePrinter::skolem_choice_definitions`. A symbol with no such
    /// provenance has no correct rendering at all, and the exporter DECLINES:
    /// the caller keeps its verdict and writes no file, because a document no
    /// checker can parse is strictly worse than no document.
    #[error(
        "proof is free in {count} symbol(s) that the problem does not declare and an Alethe \
         proof document cannot introduce ({names}); refusing to emit a document no checker \
         can parse — Carcara rejects every declaration command in a proof file"
    )]
    UndeclarableProofSymbols {
        /// How many undeclarable free symbols the proof references.
        count: usize,
        /// Comma-separated symbol names (truncated for very wide preambles).
        names: String,
    },
    /// A step's rendered text names a Skolem witness by its internal symbol
    /// after the printer resugared that witness to an inline `choice` term.
    ///
    /// The resugaring is what lets the exporter leave the witness out of the
    /// `define-fun` preamble, so a raw occurrence is an identifier the
    /// document neither defines nor the problem declares — carcara:
    /// `parser error: identifier '<name>' is not defined`, before any rule is
    /// checked. No `hole` can repair an unparseable document, so the export
    /// declines. Checked on the shipped bytes of every step
    /// (`AlethePrinter::format_step`), because the term-level guard cannot
    /// see a rendering channel: the eighth false green shipped exactly this
    /// through the producer's surface-override table.
    #[error(
        "step {id} prints Skolem witness `{name}` by its internal name after the printer \
         resugared it to a choice term; the document would be unparseable (carcara: identifier \
         is not defined), so the export declines"
    )]
    ResugaredWitnessPrintedRaw {
        /// The step whose rendering leaked the name.
        id: ProofId,
        /// The witness's internal symbol.
        name: String,
    },
}

impl AlethePrintError {
    /// Kind discriminant as a short static string, for error messages.
    fn kind_name(kind: &ay_core::TheoryLemmaKind) -> &'static str {
        match kind {
            ay_core::TheoryLemmaKind::LraFarkas => "LraFarkas",
            ay_core::TheoryLemmaKind::LiaGeneric => "LiaGeneric",
            _ => "Other",
        }
    }
}

/// The index-equality guards a read-over-write-chain subproof assumes.
///
/// Positions line up across all four vectors: entry `k` describes the `k`-th
/// DISTINCT guard literal, assumed as `(not printed[k])` under `assume_ids[k]`,
/// with `row_ids[k]` naming the step whose unit clause is the
/// `(not (= store_index read_index))` orientation `arrays_row` requires.
#[derive(Default)]
struct RowChainGuards {
    order: Vec<TermId>,
    printed: Vec<String>,
    assume_ids: Vec<String>,
    row_ids: Vec<String>,
    bridges: Vec<String>,
}

/// One bounded, exact plan for presenting an authored `let` assumption and
/// deriving the root spelling used by the rest of the proof.
struct LetAssumeBridgePlan {
    levels: Vec<(Vec<(String, String)>, String)>,
    innermost_body: String,
    eliminated: String,
    substitution_matches: bool,
}

impl LetAssumeBridgePlan {
    fn is_certified(&self) -> bool {
        self.substitution_matches
    }
}

/// What one chain walk contributes to the surrounding equality chain.
enum RowChainPathProof {
    /// The walk's value IS `(select root index)`; nothing to prove.
    Reflexive,
    /// The named step proves `(= (select root index) tail)`.
    Step(String),
}

/// Immutable inputs describing one read-over-write chain walk.
///
/// Keeping the path's mutually dependent renderings together makes it harder
/// for a caller to accidentally pair an index or tail with the wrong checked
/// path.
struct RowChainPathEmission<'a> {
    prefix: &'a str,
    read_index: TermId,
    index_str: &'a str,
    path: &'a crate::checker::RowChainPath,
    tail: &'a str,
}

/// Alethe proof printer
pub(crate) struct AlethePrinter<'a> {
    terms: &'a TermStore,
    term_overrides: Option<&'a HashMap<TermId, String>>,
    /// EXACT problem text for assumed terms whose authored `not` shells
    /// elaboration ate (`(assert (not (not phi)))` stores only `phi`).
    ///
    /// Deliberately NOT the ordinary override channel. The assumed term keeps
    /// whatever rendering the rest of the document already gives it — often a
    /// source override of its own — and this text is consulted at the `assume`
    /// leaf and nowhere else, so nothing downstream changes spelling. See
    /// [`Self::format_negation_shell_assume_bridge`].
    negation_shell_assumes: Option<&'a HashMap<TermId, String>>,
    /// The problem's nullary `define-fun` premises, printed symbol to printed
    /// body; read only by [`Self::lower_closed_guard_clause`].
    nullary_definitions: Option<&'a HashMap<String, String>>,
    /// Proof-local renderings introduced by certified Skolem expansion. These
    /// map the fresh witness to its Hilbert-choice term and propagate source
    /// surface syntax across the exact binder substitution.
    skolem_overrides: std::cell::RefCell<HashMap<TermId, String>>,
    /// Skolem steps whose instance is the store's `true` / `false` and whose
    /// authored body has a checked rewrite to it
    /// (`constant_skolem_bridge.rs`). Their instance keeps the constant's own
    /// spelling instead of acquiring the authored body as an override, which
    /// would respell every `true` / `false` in the document.
    constant_skolem_bridges:
        std::cell::RefCell<HashMap<ProofId, constant_skolem_bridge::ConstantSkolemBridge>>,
    /// Fresh witnesses rendered as `choice`, hence never free declarations.
    skolem_witness_names: std::cell::RefCell<HashSet<String>>,
    /// The printed name of every variable an IR `Anchor` binds anywhere in
    /// the proof, recorded by `prepare_proof`. Clean refuses a `dt_project`
    /// step under an anchor that binds its selector or constructor name, so
    /// the lowering (`dt_project.rs`) declines on any of these names.
    anchor_binder_names: std::cell::RefCell<HashSet<String>>,
    /// Memoized `format_term` results. Terms form a DAG and proof steps
    /// repeat literals heavily, so uncached recursive formatting is
    /// superquadratic in proof size (the PEQ Alethe-export hotspot). The
    /// cache is purely an amortization: identical strings, identical output.
    format_cache: std::cell::RefCell<HashMap<TermId, String>>,
    /// Terms of already-printed `assume` steps, recorded as `format_step`
    /// walks the proof in order (premises always refer to earlier steps).
    /// Used to resugar decomposition steps whose premise assume PRINTS as a
    /// De Morgan surface form (`(not (and ...))` for an internal or-term).
    assume_terms: std::cell::RefCell<HashMap<ProofId, TermId>>,
    /// Renderings installed by the `let`-elimination bridge (see
    /// [`Self::format_let_assume_bridge`]).
    ///
    /// A `let`-rooted surface override is unusable in every DOWNSTREAM step: no
    /// Alethe tautology has a `(let ...)` gate, and carcara's `assume`/premise
    /// matching never expands `let` (`Polyeq` recurses through `Term::Let` via
    /// `compare_binder`, it does not eliminate it). The bridge keeps the
    /// `assume` in the problem's surface spelling and derives the eliminated
    /// form once; from that point on the term must print as the eliminated
    /// form everywhere, which is what this map does. Read BEFORE
    /// `term_overrides` so the switch is atomic for the whole document.
    ///
    /// The FOLDED-conjunction assume bridge ([`Self::plan_folded_and_assumes`])
    /// uses the same channel for the same reason, and installs its entries
    /// EAGERLY in `prepare_proof` rather than at the assume, so no step printed
    /// before the assume can observe the authored spelling.
    let_bridge_renderings: std::cell::RefCell<HashMap<TermId, String>>,
    /// Authored spellings that may be printed ONLY at their own `assume`.
    ///
    /// Populated by [`Self::plan_folded_and_assumes`] for every assumed term
    /// whose surface override is an authored conjunction that elaboration
    /// FOLDED away. The spelling has to reach the `assume` (that is what the
    /// external checker matches against the problem file) and must reach
    /// nothing else (it does not denote the folded term the rest of the
    /// document derives from).
    folded_assume_surfaces: std::cell::RefCell<HashMap<TermId, String>>,
    /// Exact problem spellings confined to their own reachable `assume`.
    /// [`Self::plan_equivalent_authored_assumes`] installs canonical rendering
    /// document-wide and emits a checked local equivalence bridge.
    authored_assume_surfaces: std::cell::RefCell<HashMap<TermId, String>>,
    /// Exact proof ids whose authored assumptions are consumed and therefore
    /// need a checked bridge back to canonical spelling. Kept per id rather
    /// than per term: a proof may contain several consumed `Assume` rows for
    /// one interned term, and each row emits (and must be charged for) its own
    /// bridge.
    authored_assume_bridged: std::cell::RefCell<HashSet<ProofId>>,
    /// Override-bearing terms whose every `Assume` row is unused.
    ///
    /// Their authored spelling is still required at those `assume` commands,
    /// but no proof edge licenses that spelling at any other occurrence. The
    /// term formatter therefore suppresses the ordinary override for this
    /// exact set, and the assume formatter retrieves it explicitly.
    assume_only_override_terms: std::cell::RefCell<HashSet<TermId>>,
    /// Authored-assume terms whose checked source-to-canonical bridge is the
    /// narrow two-row `la_generic` implication rather than a Boolean
    /// equivalence derivation.
    linear_arithmetic_assume_bridges: std::cell::RefCell<HashSet<TermId>>,
    /// Authored-assume terms whose checked source-to-canonical bridge is
    /// `distinct_elim` (+ `not_symm`) from a binary authored `distinct`.
    distinct_elimination_assume_bridges: std::cell::RefCell<HashSet<TermId>>,
    /// Authored-assume terms bridged onto the DOCUMENT's rendering of the
    /// canonical term (`authored_assume::document_canonical`), by schema.
    document_canonical_assume_bridges:
        std::cell::RefCell<HashMap<TermId, authored_assume::AuthoredAssumeBridge>>,
    /// `forall_inst` steps whose authored instance spelling is confined to the
    /// step itself (`confined_forall_instance`).
    confined_forall_instances:
        std::cell::RefCell<HashMap<ProofId, confined_forall_instance::ConfinedForallInstance>>,
    /// Surface overrides visible to downstream wire-rule selection after
    /// exact authored-assume bridges confine their source text to `assume`.
    wire_term_overrides: std::cell::RefCell<Option<HashMap<TermId, String>>>,
    /// Whether [`Self::wire_term_overrides`] has passed its borrowed
    /// entry/byte/work preflight and been cloned. Keeping construction lazy is
    /// load-bearing: the clone itself must not run before that admission.
    wire_term_overrides_initialized: std::cell::Cell<bool>,
    /// The EFFECTIVE rendering table every wire-rule judgement reads:
    /// [`Self::wire_term_overrides`] overlaid with the printer's own channels
    /// ([`Self::let_bridge_renderings`], then [`Self::skolem_overrides`]), in
    /// the order `write_term_into` consults them. Cached against the three
    /// tables' sizes; see [`Self::judgement_overrides`].
    ///
    /// Until 2026-09-13 the judgements read the producer's table alone and
    /// were blind to what this printer itself spells — the ninth false green.
    #[allow(clippy::type_complexity)]
    judgement_overrides:
        std::cell::RefCell<Option<((usize, usize, usize), Option<HashMap<TermId, String>>)>>,
    /// Subset of [`Self::folded_assume_surfaces`] whose `assume` is a PREMISE
    /// of some step, and therefore owes the consumers a derivation of the
    /// folded clause. An assumption nothing consumes owes nothing and is
    /// printed unchanged — introducing a bridge (and, in the worst case, a
    /// `hole`) for it would put an unproved step into a document that had none.
    folded_assume_bridged: std::cell::RefCell<HashSet<TermId>>,
    /// The bridge root the authored-assume Boolean-fold leaf works under, with
    /// its memoized coherence (`authored_assume/boolean_fold/document_spelling.rs`).
    boolean_fold_scope: std::cell::RefCell<authored_assume::BooleanFoldScope>,
    /// The EXACT clause literals each already-emitted step put on the wire
    /// under its own id — the only thing an external checker binds to that id.
    ///
    /// Populated by `format_step` as it walks the proof in order, so a
    /// premise-bearing step always finds its premises here. Read by
    /// [`Self::judge_printed_resolution`] and `judge_printed_premise_rules`, which replay
    /// a step over the printed text rather than over the term store. Every
    /// demanded id gets an entry — its literals, or the reason it has none
    /// (`printed_resolution::PrintedClause`) — so a judgement that cannot read
    /// a premise declines to the honest hole instead of approving a step it
    /// never saw.
    printed_step_clauses: std::cell::RefCell<HashMap<ProofId, printed_resolution::PrintedClause>>,
    /// Whether `plan_printed_clause_demand` ran for this export. Inactive in
    /// an isolated helper or a unit test rendering one step, where nothing is
    /// recorded and nothing is judged; active on every ordinary export, where
    /// an unrecorded premise of a judged step is a hole, never an approval.
    printed_clause_ledger_active: std::cell::Cell<bool>,
    /// The ids some resolution-family step will cite as a premise. Only these
    /// are recorded above, so the ledger never becomes a second copy of a
    /// document whose first copy is already tens of megabytes.
    printed_clause_demand: std::cell::RefCell<HashMap<ProofId, ProofId>>,
    /// Innermost native scope end for demanded zero-extension congruence
    /// premises. A retained assumption is not authority after its anchor ends.
    native_zero_cong_scopes: std::cell::RefCell<HashMap<ProofId, ProofId>>,
    /// `(last native use, clause id)`, consumed only by the sequential exporter.
    printed_clause_retirement: std::cell::RefCell<Vec<(ProofId, ProofId)>>,
    printed_clause_retirement_cursor: std::cell::Cell<usize>,
    printed_clause_free_atom: std::cell::Cell<u32>,
    printed_clause_free_atoms: std::cell::Cell<usize>,
    /// Every DISTINCT literal text the ledger above holds, interned once and
    /// addressed by a generation-tagged slot here.
    ///
    /// A printed clause names the same atom over and over — MEASURED on QF_UF
    /// `QG-classification/qg5/iso_icl1279`, the ledger's 35,692 literal
    /// occurrences are drawn from **1,133 distinct strings**, 0.29 MiB of text
    /// — so a ledger of `String`s is mostly copies of copies. Interning makes
    /// [`Self::printed_clause_bytes`] the ledger's REAL residency, which is
    /// what the bound exists to cap.
    printed_clause_atom_texts: std::cell::RefCell<Vec<printed_resolution::PrintedAtomSlot>>,
    /// The index of [`Self::printed_clause_atom_texts`], by literal text.
    printed_clause_atom_index: std::cell::RefCell<
        HashMap<printed_resolution::WireLiteral, printed_resolution::PrintedAtomId>,
    >,
    printed_clause_bodies: std::cell::RefCell<HashMap<printed_resolution::OwnedText, usize>>,
    /// Retained heap storage charged to the 8 MiB ledger bound: plan and table
    /// capacities, atom slots, owned text allocations and clause id buffers.
    /// Retiring text never refunds allocated table or slot capacity.
    printed_clause_bytes: std::rc::Rc<printed_resolution::ChargeState>,
    printed_clause_overhead_bytes: std::cell::Cell<usize>,
    printed_replay_scratch: std::cell::RefCell<Option<printed_resolution::TextBudget>>,
    /// The replay identity of every printed literal a judgement has decoded —
    /// its atom, that atom's normalised spelling, and the parity of its `not`
    /// shells. A premise clause is cited by many steps; without this memo each
    /// citation re-parsed the same text, and the emission work budget was
    /// charged for it every time.
    printed_literal_identities:
        std::cell::RefCell<HashMap<std::rc::Rc<str>, printed_resolution::PrintedLiteral>>,
    printed_wire_identities: std::cell::RefCell<
        HashMap<printed_resolution::WireLiteral, printed_resolution::PrintedLiteral>,
    >,
    /// Bytes that memo occupies, capped like the ledger it serves.
    printed_literal_identity_bytes: std::cell::Cell<usize>,
    /// Internal clauses by proof id, populated eagerly so a resolution step
    /// can repair surface-order complements in its already-printed premises.
    proof_clauses: std::cell::RefCell<HashMap<ProofId, Vec<TermId>>>,
    /// The EXACT text an already-emitted plain `assume` command concluded,
    /// keyed by its proof id.
    ///
    /// Recorded only on the ordinary `(assume {id} {term})` path: the three
    /// authored/folded/`let` assume bridges conclude a DERIVED form under the
    /// step id and their conclusion text is not this string, so recording them
    /// here would let a consumer cite an id for a clause it does not carry.
    /// Populated as `format_step` walks the proof in order, so every entry is
    /// a hypothesis already printed ABOVE the step reading it.
    assume_printed: std::cell::RefCell<HashMap<ProofId, String>>,
    /// Accumulated rendering work; see [`AlethePrintError::EmissionBudgetExhausted`].
    work: std::cell::Cell<u64>,
    /// Optional cap on `work` (#A2b, synthesized-default emission only).
    work_budget: Option<u64>,
    /// One borrowed, sticky owner observation across planning and rendering.
    emission_progress: emission_progress::EmissionProgress<'a>,
    /// Shared proof-wide admission for the expensive arithmetic `poly_simp`
    /// promotion. `prepare_proof` replaces the standalone default with a cheap
    /// whole-document preflight before any step is rendered.
    poly_simp_promotion_budget: std::cell::RefCell<crate::wire_rule::ArithPolySimpPromotionBudget>,
    /// Whether, and until when, a support question may be answered by the
    /// complete bit-blast (`complete_blast/ask.rs`).
    complete_blast: CompleteBlastAsk<'a>,
    /// The asking solve's record of its screen's declines, which a render
    /// asked from inside that solve reads (`bv_support_memo/within_solve.rs`).
    support_declines: Option<&'a BvSupportDeclines>,
}

impl<'a> AlethePrinter<'a> {
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        Self::new_with_overrides(terms, None)
    }

    pub(crate) fn new_with_overrides(
        terms: &'a TermStore,
        term_overrides: Option<&'a HashMap<TermId, String>>,
    ) -> Self {
        Self::new_with_overrides_and_budget(terms, term_overrides, None)
    }

    pub(crate) fn new_with_overrides_and_budget(
        terms: &'a TermStore,
        term_overrides: Option<&'a HashMap<TermId, String>>,
        work_budget: Option<u64>,
    ) -> Self {
        Self {
            terms,
            term_overrides,
            negation_shell_assumes: None,
            nullary_definitions: None,
            skolem_overrides: std::cell::RefCell::new(HashMap::default()),
            constant_skolem_bridges: std::cell::RefCell::new(HashMap::default()),
            skolem_witness_names: std::cell::RefCell::new(HashSet::default()),
            anchor_binder_names: std::cell::RefCell::new(HashSet::default()),
            format_cache: std::cell::RefCell::new(HashMap::default()),
            assume_terms: std::cell::RefCell::new(HashMap::default()),
            let_bridge_renderings: std::cell::RefCell::new(HashMap::default()),
            folded_assume_surfaces: std::cell::RefCell::new(HashMap::default()),
            authored_assume_surfaces: std::cell::RefCell::new(HashMap::default()),
            authored_assume_bridged: std::cell::RefCell::new(HashSet::default()),
            assume_only_override_terms: std::cell::RefCell::new(HashSet::default()),
            printed_step_clauses: std::cell::RefCell::new(HashMap::default()),
            printed_clause_ledger_active: std::cell::Cell::new(false),
            printed_clause_demand: std::cell::RefCell::new(HashMap::default()),
            native_zero_cong_scopes: std::cell::RefCell::new(HashMap::default()),
            printed_clause_retirement: std::cell::RefCell::new(Vec::new()),
            printed_clause_retirement_cursor: std::cell::Cell::new(0),
            printed_clause_free_atom: std::cell::Cell::new(u32::MAX),
            printed_clause_free_atoms: std::cell::Cell::new(0),
            printed_clause_atom_texts: std::cell::RefCell::new(Vec::new()),
            printed_clause_atom_index: std::cell::RefCell::new(HashMap::default()),
            printed_clause_bodies: std::cell::RefCell::new(HashMap::default()),
            printed_clause_bytes: std::rc::Rc::new(printed_resolution::ChargeState::root()),
            printed_clause_overhead_bytes: std::cell::Cell::new(0),
            printed_replay_scratch: std::cell::RefCell::new(None),
            printed_literal_identities: std::cell::RefCell::new(HashMap::default()),
            printed_wire_identities: std::cell::RefCell::new(HashMap::default()),
            printed_literal_identity_bytes: std::cell::Cell::new(0),
            linear_arithmetic_assume_bridges: std::cell::RefCell::new(HashSet::default()),
            distinct_elimination_assume_bridges: std::cell::RefCell::new(HashSet::default()),
            document_canonical_assume_bridges: std::cell::RefCell::new(HashMap::default()),
            confined_forall_instances: std::cell::RefCell::new(HashMap::default()),
            wire_term_overrides: std::cell::RefCell::new(None),
            wire_term_overrides_initialized: std::cell::Cell::new(false),
            judgement_overrides: std::cell::RefCell::new(None),
            folded_assume_bridged: std::cell::RefCell::new(HashSet::default()),
            boolean_fold_scope: std::cell::RefCell::new(Default::default()),
            proof_clauses: std::cell::RefCell::new(HashMap::default()),
            assume_printed: std::cell::RefCell::new(HashMap::default()),
            work: std::cell::Cell::new(0),
            work_budget,
            emission_progress: Default::default(),
            poly_simp_promotion_budget: std::cell::RefCell::new(
                crate::wire_rule::ArithPolySimpPromotionBudget::standalone(),
            ),
            complete_blast: CompleteBlastAsk::Asked,
            support_declines: None,
        }
    }

    /// Attach one caller observation without granting any proof authority.
    pub(crate) fn with_emission_progress(mut self, caller: &'a mut dyn FnMut() -> bool) -> Self {
        self.emission_progress = emission_progress::EmissionProgress::with_caller(caller);
        self
    }

    fn with_parent_emission_progress(mut self, parent: &AlethePrinter<'a>) -> Self {
        self.emission_progress = parent.emission_progress.clone();
        self.complete_blast = parent.complete_blast;
        self
    }

    /// Ask the complete bit-blast only as `ask` says ([`CompleteBlastAsk`]).
    #[must_use]
    pub(crate) fn asking_complete_blast(mut self, ask: CompleteBlastAsk<'a>) -> Self {
        self.complete_blast = ask;
        self
    }

    /// Both the original emission owner and the support question must admit
    /// every blast lane and retained answer. Neither control grants a budget.
    fn complete_blast_progress(&self) -> Option<()> {
        self.check_emission_progress(0).ok()?;
        match self.complete_blast {
            CompleteBlastAsk::NotAsked => None,
            _ => self.complete_blast_keeps_going().then_some(()),
        }
    }

    /// Attach the authored `not`-shell spellings for `assume` leaves.
    #[must_use]
    pub(crate) fn with_negation_shell_assumes(
        mut self,
        negation_shell_assumes: Option<&'a HashMap<TermId, String>>,
    ) -> Self {
        self.negation_shell_assumes = negation_shell_assumes;
        self
    }

    /// Print an `assume` in the problem's own spelling and DERIVE the term the
    /// rest of the document uses, when elaboration ate the authored negation
    /// shells.
    ///
    /// `(assert (not (not phi)))` is an ordinary SMT-LIB idiom (every CVC3
    /// translation in `QF_ABV/egt` writes it), and `TermStore::mk_not`
    /// eliminates the double negation at term CONSTRUCTION, so the proof's
    /// `Assume` row holds `phi` and the exported leaf claimed a premise the
    /// problem does not state:
    ///
    /// ```text
    /// [ERROR] checking failed on step 't0' with rule 'assume': could not match
    ///         term to any of the original problem premises: (= ...)
    /// ```
    ///
    /// Alethe's `not_not` is `(cl (not (not (not psi))) psi)`, so with
    /// `psi = S(j-1)` its first literal is exactly `(not S(j))` and one
    /// resolution against the shell above peels one pair. The last resolution
    /// carries the ORIGINAL id, concluding exactly the unit clause every
    /// downstream premise already cites, so nothing else in the document moves.
    ///
    /// FAILS CLOSED. The authored text must be exactly `k` shells over
    /// `format_term`'s own rendering of the term — the text the rest of the
    /// document uses, which is the source-override spelling wherever one is in
    /// play. Anything else and the export declines rather than printing a leaf
    /// nobody derived.
    fn format_negation_shell_assume_bridge(
        &self,
        id: ProofId,
        term: TermId,
    ) -> Result<Option<String>, AlethePrintError> {
        let Some(surface) = self
            .negation_shell_assumes
            .and_then(|shells| shells.get(&term))
        else {
            return Ok(None);
        };
        let canonical = self.format_term(term);
        let Some(pairs) = negation_shell_assume_surface_pairs(surface, &canonical) else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "an authored assume spelling is not the printed term under negation shells"
                    .to_string(),
            });
        };
        self.charge((surface.len() as u64).saturating_mul(pairs as u64 + 2));
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(0));
        }
        let mut output = format!("(assume {id}.a {surface})");
        let mut premise = format!("{id}.a");
        for peeled in 0..pairs {
            let level = pairs - peeled;
            let outer = authored_assume::negation_shell_rendering(&canonical, level);
            let inner = authored_assume::negation_shell_rendering(&canonical, level - 1);
            let target = if level == 1 {
                format!("{id}")
            } else {
                format!("{id}.r{level}")
            };
            output.push_str(&format!(
                "\n(step {id}.n{level} (cl (not {outer}) {inner}) :rule not_not)\
                 \n(step {target} (cl {inner}) :rule resolution :premises ({premise} {id}.n{level}))"
            ));
            premise = target;
        }
        Ok(Some(output))
    }

    /// Prepare every certified Skolem mapping before any declaration or proof
    /// step is emitted. This is intentionally eager: arithmetic/theory steps
    /// may mention the witness before the `sko_forall` step's proof ID.
    pub(crate) fn prepare_proof(&self, proof: &Proof) -> Result<(), AlethePrintError> {
        self.check_emission_progress(0)?;
        // This must precede the proof-clause copies below. In particular, an
        // over-cap override ledger may not allocate its clone (or trigger other
        // eager proof preparation) before the borrowed fail-closed preflight.
        self.initialize_wire_term_overrides()?;
        *self.poly_simp_promotion_budget.borrow_mut() =
            crate::wire_rule::ArithPolySimpPromotionBudget::for_proof(proof);
        {
            let mut clauses = self.proof_clauses.borrow_mut();
            clauses.clear();
            self.printed_step_clauses.borrow_mut().clear();
            self.plan_printed_clause_demand(proof);
            *self.anchor_binder_names.borrow_mut() = proof
                .steps
                .iter()
                .filter_map(|step| match step {
                    ProofStep::Anchor { variables, .. } => Some(variables),
                    _ => None,
                })
                .flatten()
                .map(|(name, _)| quote_symbol(name))
                .collect();
            for (index, step) in proof.steps.iter().enumerate() {
                let id = ProofId(index as u32);
                if let ProofStep::NraSos {
                    clause,
                    certificate,
                } = step
                {
                    self.preflight_nra_sos_step(id, clause, certificate)?;
                }
                let clause = match step {
                    ProofStep::Assume(term) => Some(vec![*term]),
                    ProofStep::Resolution { clause, .. }
                    | ProofStep::TheoryLemma { clause, .. }
                    | ProofStep::FiniteFieldLinear { clause, .. }
                    | ProofStep::NraSos { clause, .. }
                    | ProofStep::Step { clause, .. } => Some(clause.clone()),
                    ProofStep::Anchor { .. } => None,
                    _ => None,
                };
                if let Some(clause) = clause {
                    clauses.insert(id, clause);
                }
            }
        }
        // Must precede every emission: an authored conjunction that FOLDED may
        // not be substituted for the folded term in any step, including steps
        // printed before its own `assume`.
        self.plan_equivalent_authored_assumes(proof)?;
        self.plan_folded_and_assumes(proof);
        // Only a STRUCTURAL gap refuses the document here. A sort or symbol
        // spelling pinned Carcara cannot parse (`Seq`, `FloatingPoint`, `Char`,
        // the Z3 escape extension) renders what the strict checker accepted and
        // is disclosed to the consumer through `carcara_proof_surface` (D7,
        // 2026-09-22); refusing it here withdrew every Seq-carrying artifact
        // from consumers that never claimed a Carcara check.
        if let Some(reason) = carcara_structural_gap(proof, self.terms, self.term_overrides) {
            return Err(AlethePrintError::UnavailableAuthenticatedSurface { reason });
        }
        crate::checker::quantifier::validate_sko_forall_uniqueness(proof, self.terms).map_err(
            |err| AlethePrintError::InvalidSkolemStep {
                id: match err {
                    crate::ProofCheckError::InvalidBooleanRule { step, .. } => step,
                    _ => ProofId(0),
                },
                reason: err.to_string(),
            },
        )?;

        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: ay_core::AletheRule::Skolem,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            let id = ProofId(index as u32);
            crate::checker::quantifier::validate_sko_forall(
                self.terms,
                id,
                clause,
                premises.len(),
                args,
            )
            .map_err(|err| AlethePrintError::InvalidSkolemStep {
                id,
                reason: err.to_string(),
            })?;
            let [equality] = clause.as_slice() else {
                unreachable!("strict Skolem validation fixed the clause arity")
            };
            let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
                unreachable!("strict Skolem validation fixed the equality shape")
            };
            debug_assert_eq!(eq, "=");
            let (quantified, instance) = (equality_args[0], equality_args[1]);
            // The strict validator admits BOTH readings: `sko_forall` over a
            // `forall` source and `sko_ex` over a registered positive
            // `exists` source. The exists choice binds the UNNEGATED body.
            let (bindings, body, source_is_exists) = match self.terms.get(quantified) {
                TermData::Forall(bindings, body, _) => (bindings, body, false),
                TermData::Exists(bindings, body, _) => (bindings, body, true),
                _ => unreachable!("strict Skolem validation fixed the source shape"),
            };
            let [(binder, binder_sort)] = bindings.as_slice() else {
                unreachable!("strict Skolem validation fixed the binder arity")
            };
            let [witness] = args.as_slice() else {
                unreachable!("strict Skolem validation fixed the witness arity")
            };

            let (binder_token, body_surface) = self.skolem_surface_binder_and_body(
                quantified,
                *body,
                binder,
                if source_is_exists { "exists" } else { "forall" },
            );
            // The sort is spelled the way the structural quantifier rendering
            // spells it (`format_quantifier`), not through `Sort`'s `Display`,
            // which leaves an uninterpreted sort name unquoted: one sort, one
            // spelling, at the anchor, the `choice` and the quantifier alike.
            let binder_sort = format_sort_alethe(binder_sort);
            let choice = if source_is_exists {
                format!("(choice (({binder_token} {binder_sort})) {body_surface})")
            } else {
                format!("(choice (({binder_token} {binder_sort})) (not {body_surface}))")
            };
            self.insert_skolem_override(id, *witness, choice.clone())?;
            // An instance the store folded to `true` / `false` keeps the
            // constant's spelling: keying the authored instance text on the
            // SHARED constant would respell every `true` / `false` in the
            // document. The anchor derives `(= BODY b)` instead.
            if let Some(bridge) = self.constant_skolem_bridge_for_instance(instance, &body_surface)
            {
                self.record_constant_skolem_bridge(id, &body_surface, bridge);
            } else {
                let instance_surface = substitute_smt_symbol(&body_surface, &binder_token, &choice);
                self.insert_skolem_override(id, instance, instance_surface)?;
                self.register_substituted_surface_overrides(
                    id,
                    *body,
                    instance,
                    binder,
                    &binder_token,
                    *witness,
                    &choice,
                )?;
                self.prepare_flattened_implication_overrides(
                    proof,
                    id,
                    *body,
                    instance,
                    &binder_token,
                    &choice,
                    &body_surface,
                )?;
            }
            let TermData::Var(witness_name, _) = self.terms.get(*witness) else {
                unreachable!("strict Skolem validation fixed witness shape")
            };
            self.skolem_witness_names
                .borrow_mut()
                .insert(witness_name.clone());
        }
        self.prepare_array_extensionality_choices(proof);
        // LAST, once every witness has its `choice`: no rendering the
        // document consults may still spell a resugared witness by its
        // internal symbol.
        let respelled = self.respell_renderings_naming_witnesses();
        // Preparation may have formatted source terms before their substituted
        // overrides were installed. Never retain a stale rendering.
        self.format_cache.borrow_mut().clear();
        // After every channel above is final, so an instance at a Skolem
        // witness is planned against the witness's `choice` spelling
        // (`confined_forall_instance.rs`).
        self.plan_confined_forall_instances(proof, &respelled);
        // Last: a certified `let` spelling's eliminated rendering must be the
        // one its `assume` bridge recomputes (`let_assume_confinement.rs`).
        self.confine_certified_let_assumes(proof);
        Ok(())
    }

    /// Install the epsilon (`choice`) rendering of every array-extensionality
    /// diff witness, so that EVERY downstream occurrence of the solver's fresh
    /// Skolem constant prints as the exact term Carcara's `arrays_ext` rule
    /// builds for itself.
    ///
    /// AY's internal certificate names the diff index with a fresh constant
    /// `__ay_ext_diff!N`, licensed by an `array_ext_diff_intro` provenance step
    /// plus `ExtDiffRegistry` freshness. Carcara has no such notion: its
    /// `arrays_ext` conclusion is fixed to
    /// `(not (= (select a K) (select b K)))` with
    /// `K = (choice ((x <Index>)) (or (= a b) (not (= (select a x) (select b x)))))`,
    /// and the pinned build compares that term with `assert_polyeq`, which does
    /// NOT quotient by alpha-renaming — the binder must literally be `x` (this
    /// was MEASURED: an otherwise-identical proof with binder `zz` is rejected).
    ///
    /// Rendering the constant as `K` at every occurrence is a global
    /// substitution of a term for a constant, which preserves every rule
    /// instance the document contains (all of `arrays_idx`, `arrays_row`,
    /// `cong`, `trans`, `symm`, `resolution`, `or_pos`, `or_neg`, `not_not` are
    /// schematic in their operands). It is done through the existing
    /// `skolem_overrides` channel, so the witness also stops being emitted as a
    /// free `(declare-fun ...)`.
    ///
    /// Everything here is best effort and FAIL-CLOSED: a witness that is not
    /// installed simply keeps its constant rendering, and
    /// [`Self::format_array_extensionality`] then refuses the lemma exactly as
    /// before.
    fn prepare_array_extensionality_choices(&self, proof: &Proof) {
        let mut pending: Vec<(TermId, TermId, TermId)> = Vec::new();
        for step in &proof.steps {
            let ProofStep::TheoryLemma { clause, kind, .. } = step else {
                continue;
            };
            if !matches!(kind, ay_core::TheoryLemmaKind::ArrayExtensionality) {
                continue;
            }
            // One level only. A multi-level chain (and the datatype lane's
            // folded shape) has no single `arrays_ext` instance, so it stays
            // un-substituted and the lemma printer fails closed.
            let Some((array_a, array_b, witness)) =
                crate::checker::recognize_array_extensionality(self.terms, clause)
            else {
                continue;
            };
            pending.push((witness, array_a, array_b));
        }
        if pending.is_empty() {
            return;
        }

        // One witness may only ever stand for ONE array pair: a substitution
        // that satisfied one lemma while contradicting another would corrupt
        // every step in between. A witness that already has a certified
        // `sko_forall` rendering is likewise left alone.
        let mut pairs: HashMap<TermId, Option<(TermId, TermId)>> = HashMap::default();
        for &(witness, array_a, array_b) in &pending {
            let entry = pairs.entry(witness).or_insert(Some((array_a, array_b)));
            if *entry != Some((array_a, array_b)) {
                *entry = None;
            }
        }
        let mut kept: HashSet<TermId> = HashSet::default();
        pending.retain(|&(witness, array_a, array_b)| {
            !self.skolem_overrides.borrow().contains_key(&witness)
                && pairs.get(&witness) == Some(&Some((array_a, array_b)))
                && kept.insert(witness)
        });
        if pending.is_empty() {
            return;
        }

        // A witness whose own arrays mention another witness must be rendered
        // AFTER that one, or its choice body would bake in the stale constant.
        // `ExtDiffRegistry` already forbids cycles; a cycle here simply leaves
        // the remaining witnesses uninstalled (fail-closed).
        let mut remaining = pending;
        loop {
            let uninstalled: Vec<TermId> = remaining.iter().map(|&(w, _, _)| w).collect();
            let mut installed_any = false;
            let mut next = Vec::new();
            for &(witness, array_a, array_b) in &remaining {
                let blocked = uninstalled.iter().any(|&other| {
                    other != witness
                        && (term_mentions(self.terms, array_a, other)
                            || term_mentions(self.terms, array_b, other))
                });
                if blocked {
                    next.push((witness, array_a, array_b));
                    continue;
                }
                // Capture guard: the binder is literally `x`, so a free `x` of
                // any sort inside either array would be captured by it.
                if term_mentions_symbol(self.terms, array_a, EXT_CHOICE_BINDER)
                    || term_mentions_symbol(self.terms, array_b, EXT_CHOICE_BINDER)
                {
                    continue;
                }
                let TermData::Var(witness_name, _) = self.terms.get(witness) else {
                    continue;
                };
                let witness_name = witness_name.clone();
                // Renderings computed before the previous pass's installs are
                // stale for any term containing an inner witness.
                self.format_cache.borrow_mut().clear();
                let choice = self.array_ext_choice_term(array_a, array_b, witness);
                if self
                    .insert_skolem_override(ProofId(0), witness, choice)
                    .is_err()
                {
                    continue;
                }
                self.skolem_witness_names.borrow_mut().insert(witness_name);
                installed_any = true;
            }
            if next.is_empty() || !installed_any {
                break;
            }
            remaining = next;
        }
        self.format_cache.borrow_mut().clear();
    }

    /// The exact epsilon term Carcara's `arrays_ext` builds for `(a, b)`.
    fn array_ext_choice_term(&self, array_a: TermId, array_b: TermId, witness: TermId) -> String {
        let a = self.format_term(array_a);
        let b = self.format_term(array_b);
        let sort = format_sort_alethe(self.terms.sort(witness));
        let binder = EXT_CHOICE_BINDER;
        format!(
            "(choice (({binder} {sort})) \
             (or (= {a} {b}) (not (= (select {a} {binder}) (select {b} {binder})))))"
        )
    }

    /// Select the binder token and body spelling used by every command in one
    /// expanded `sko_forall` / `sko_ex`.  A whole-quantifier surface override
    /// is the authority when present: using the internal body beside an
    /// authored `(=> ...)` quantifier produces an invalid mixed-identity
    /// anchor.
    ///
    /// `keyword` is the printed quantifier's own head — `forall` for
    /// `sko_forall`, `exists` for `sko_ex`. Until 2026-09-13 this read a
    /// `forall` override only, so a positive authored `exists` whose binder
    /// the store had renamed (`z` to `z_3`) fell through to the internal
    /// binder and the canonical body: the document printed the AUTHORED
    /// quantifier `(exists ((z Int)) ..)` beside an anchor binding `z_3` to a
    /// `choice` over the canonical body, and pinned carcara refused it
    /// (`BindingIsNotInContext`) under a green flag on main — the eighth
    /// shape's `sko_ex` sibling. The one-spelling rule is the same as for
    /// `forall`: the anchor binds the printed quantifier's own binder, the
    /// `choice` closes over the printed body, and the instance is that body
    /// under `binder := choice`.
    ///
    /// For an `exists` the authored body is carried only when it has the
    /// internal body's LOGICAL SKELETON
    /// ([`Self::printed_body_corresponds_to_internal`]). The instance's
    /// projections (`and_pos` over the Skolemized conjunction) are read
    /// STRUCTURALLY by the checker, so an authored `(not (or A B))` that the
    /// store De Morgan'd into `(and (not A) (not B))`, or an authored two-
    /// conjunct `and` the store flattened into three, cannot be the
    /// instance's spelling without re-deriving every projection — MEASURED:
    /// carrying either declined the whole export at the first `and_pos`, and
    /// a declined export is strictly worse than the honest hole the internal
    /// spelling yields (the verdict still exits 0 under `--proof`). The head
    /// comparison this guard started as was not enough: it passed the
    /// flattening, because flattening does not change the head. The `forall`
    /// arm is unchanged: its De Morgan shapes have their own resugaring
    /// (`prepare_flattened_implication_overrides`).
    ///
    /// An `exists` body the store folded to `true` / `false` has no skeleton
    /// to compare and no projection to protect: its instance is the constant
    /// itself. The authored body is carried there exactly when
    /// [`Self::constant_skolem_bridge_for_instance`] derives that constant
    /// from it, so the anchor and the `sko_ex` read the quantifier's own
    /// body (`(exists ((q Int)) (not (= q q)))`, which the base holed).
    fn skolem_surface_binder_and_body(
        &self,
        quantified: TermId,
        body: TermId,
        internal_binder: &str,
        keyword: &str,
    ) -> (String, String) {
        if let Some(surface) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&quantified))
        {
            if let Some((binder, surface_body)) = split_single_binder_quantifier(surface, keyword) {
                if keyword == "forall"
                    || self.printed_body_corresponds_to_internal(&surface_body, body)
                    || self
                        .constant_skolem_bridge_for_instance(body, &surface_body)
                        .is_some()
                {
                    return (binder, surface_body);
                }
            }
        }
        let binder = quote_symbol(internal_binder);
        let body = self
            .term_overrides
            .and_then(|overrides| overrides.get(&body))
            .cloned()
            .unwrap_or_else(|| self.format_term(body));
        (binder, body)
    }

    /// Whether a printed body can stand in for `term` everywhere the
    /// document reads the body's SHAPE.
    ///
    /// The authored spelling of a Skolemized `exists` body is carried into
    /// the anchor, the `choice` and — through `substitute_smt_symbol` — the
    /// instance that every later step projects. Those projections are read
    /// STRUCTURALLY by the checker: `and_pos :args (k)` wants the k-th
    /// top-level operand of the printed source, `or_pos` compares the gate's
    /// arity against the clause tail. So the question the guard has to answer
    /// is not "do the two heads agree" but "do the printed body and the
    /// effective source have the same logical skeleton".
    ///
    /// Until 2026-09-16 it compared the TOP-LEVEL HEAD TOKEN only, and that
    /// is not the same question. MEASURED on `(exists ((z Int)) (and (>= z 0)
    /// (not (or (< z 0) (>= (g z) z)))))`: the authored head is `and` and the
    /// store's is `and`, so the guard passed and the authored body was
    /// carried — but the store had De Morgan'd the second conjunct and
    /// FLATTENED the result, so its `and` has three operands against the
    /// authored two. `and_pos :args (2)` then had no conjunct 2 to project,
    /// `surface_and_pos` declined and the WHOLE EXPORT was refused: no
    /// document in the default posture, `unknown` under `--strict-proofs`
    /// (an `unsat` → `unknown` MOVE) and exit 1 with no verdict under
    /// `--proof FILE`, where the base ships a two-hole document and exits 0
    /// in all three. A guard whose failure mode is worse than not guarding is
    /// not a guard.
    ///
    /// The skeleton is walked through the connectives the structural rules
    /// read — `not`, `and`, `or`, `=>`, `xor`, `ite` and `=` — where the head
    /// AND the arity must agree, which is what refuses an n-ary flattening or
    /// a De Morgan'd operand. A theory atom is opaque: it is where the store's
    /// normalisation lives (`(>= z 0)` against `(<= 0 z_3)`), every rule that
    /// reads the skeleton treats it as one leaf, and the `and_pos` bridge
    /// already derives a normalised operand from the authored one. Its
    /// OPERANDS are therefore not compared, but an atom may not stand where
    /// the store has an application, nor an application where the store has a
    /// leaf.
    ///
    /// Where the correspondence cannot be established the caller falls back
    /// to the store's own spelling, which is what the base prints: an honest
    /// `sko_ex` hole in a published document, never a refused export.
    fn printed_body_corresponds_to_internal(&self, printed: &str, term: TermId) -> bool {
        self.printed_shape_corresponds(printed, term, true, 0)
    }

    fn printed_shape_corresponds(
        &self,
        printed: &str,
        term: TermId,
        root: bool,
        depth: usize,
    ) -> bool {
        if depth > MAX_SURFACE_SKELETON_DEPTH {
            return false;
        }
        let printed = printed.trim();
        let fields = printed_application_fields(printed);
        let head = fields
            .as_ref()
            .map(|fields| quantifier_surface::bare_symbol(fields[0]));
        match self.terms.get(term) {
            TermData::Not(inner) => {
                let Some(fields) = fields.as_ref() else {
                    return false;
                };
                head == Some("not")
                    && fields.len() == 2
                    && self.printed_shape_corresponds(fields[1], *inner, false, depth + 1)
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let Some(fields) = fields.as_ref() else {
                    return false;
                };
                head == Some("ite")
                    && fields.len() == 4
                    && [*condition, *then_branch, *else_branch]
                        .into_iter()
                        .enumerate()
                        .all(|(index, operand)| {
                            self.printed_shape_corresponds(
                                fields[index + 1],
                                operand,
                                false,
                                depth + 1,
                            )
                        })
            }
            TermData::App(symbol, args) if !args.is_empty() => {
                let Some(fields) = fields.as_ref() else {
                    return false;
                };
                if is_structural_connective(symbol.name()) {
                    return head == Some(symbol.name())
                        && fields.len() == args.len() + 1
                        && args.iter().enumerate().all(|(index, operand)| {
                            self.printed_shape_corresponds(
                                fields[index + 1],
                                *operand,
                                false,
                                depth + 1,
                            )
                        });
                }
                // A theory atom. Its printed head has to be the atom's own
                // symbol or, below the root, a spelling the store is KNOWN
                // to have normalised into it (`store_normalised_atom_head`).
                //
                // Until 2026-09-16 this arm ended `!root || head ==
                // Some(symbol.name())`: below the root ANY printed
                // application of any head and any arity was accepted as the
                // atom's spelling. MEASURED on `(exists ((z Int)) (not (or
                // (< 0 (- 0 1)) (>= (g z) z))))`: the store folds `(< 0 (- 0
                // 1))` to `false` and `(or false B)` to `B`, so its body is
                // `(not B)`; the authored `(not (or A B))` passed the `not`
                // arm, and at depth 1 the printed `(or A B)` met the store
                // atom `B` and was ACCEPTED. The carried body mixed the two
                // identities, `judge_printed_resolution` refused the export
                // at `t16`, and a document the base publishes with two
                // honest holes became no document, `unknown` under
                // `--strict-proofs` and exit 1 under `--proof FILE`. A
                // connective is never an atom's spelling.
                head.is_some_and(|head| {
                    head == symbol.name()
                        || (!root && store_normalised_atom_head(head, symbol.name()))
                })
            }
            TermData::Var(..) | TermData::Const(..) | TermData::App(..) => fields.is_none(),
            _ => false,
        }
    }

    /// Propagate an authored implication's operand spellings to the literals
    /// of AY's flattened internal or-term.
    ///
    /// Elaboration represents `(=> (and A1 .. An) B)` as the canonical n-ary
    /// `(or (not A1) .. (not An) B)`.  The proof tracker correctly records
    /// `or_neg` tautologies over that internal term; once the quantified source
    /// is printed with its authored implication syntax, those tautologies must
    /// be resugared to `implies_neg{1,2}` (and an `and_pos` projection for each
    /// `Ai`).  This pass maps only exact complement pairs already present in
    /// the strictly checked proof.  Any implication-shaped surface override
    /// that cannot be matched fails closed instead of emitting mixed syntax.
    #[allow(clippy::too_many_arguments)]
    fn prepare_flattened_implication_overrides(
        &self,
        proof: &Proof,
        id: ProofId,
        source_body: TermId,
        instance: TermId,
        surface_binder: &str,
        choice: &str,
        body_surface: &str,
    ) -> Result<(), AlethePrintError> {
        let Some((antecedent, consequent)) = split_binary_implies(body_surface) else {
            return Ok(());
        };
        let antecedent_parts =
            split_application(&antecedent, "and").unwrap_or_else(|| vec![antecedent.clone()]);
        let TermData::App(source_symbol, source_disjuncts) = self.terms.get(source_body) else {
            return Err(AlethePrintError::InvalidSkolemStep {
                id,
                reason: "surface implication does not correspond to an internal or-term"
                    .to_string(),
            });
        };
        let TermData::App(instance_symbol, instance_disjuncts) = self.terms.get(instance) else {
            return Err(AlethePrintError::InvalidSkolemStep {
                id,
                reason: "surface implication instance is not an internal or-term".to_string(),
            });
        };
        if source_symbol.name() != "or"
            || instance_symbol.name() != "or"
            || source_disjuncts.len() != instance_disjuncts.len()
        {
            return Err(AlethePrintError::InvalidSkolemStep {
                id,
                reason: "surface implication/internal or arity mismatch".to_string(),
            });
        }

        let mut complement_by_disjunct: HashMap<TermId, TermId> = HashMap::default();
        for step in &proof.steps {
            let ProofStep::Step {
                rule: ay_core::AletheRule::OrNeg,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            if !premises.is_empty() || args.as_slice() != [instance] || clause.len() != 2 {
                continue;
            }
            let Some(other) = clause.iter().copied().find(|&literal| literal != instance) else {
                continue;
            };
            if let Some(&disjunct) = instance_disjuncts
                .iter()
                .find(|&&disjunct| self.are_boolean_complements(disjunct, other))
            {
                complement_by_disjunct.insert(disjunct, other);
            }
        }
        if complement_by_disjunct.is_empty() {
            return Ok(());
        }

        let consequent_instance = substitute_smt_symbol(&consequent, surface_binder, choice);
        let antecedent_instances: Vec<String> = antecedent_parts
            .iter()
            .map(|part| substitute_smt_symbol(part, surface_binder, choice))
            .collect();
        let mut used_parts = vec![false; antecedent_parts.len()];
        let mut saw_consequent = false;

        for (&source_disjunct, &instance_disjunct) in
            source_disjuncts.iter().zip(instance_disjuncts)
        {
            let Some(&complement) = complement_by_disjunct.get(&instance_disjunct) else {
                continue;
            };
            if self.surface_term(source_disjunct) == consequent {
                if saw_consequent {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "surface implication consequent matched multiple disjuncts"
                            .to_string(),
                    });
                }
                saw_consequent = true;
                self.insert_skolem_override(
                    id,
                    complement,
                    format!("(not {consequent_instance})"),
                )?;
                continue;
            }

            let matches: Vec<usize> = antecedent_parts
                .iter()
                .enumerate()
                .filter_map(|(part_index, part)| {
                    self.surface_complement_matches(source_disjunct, part)
                        .then_some(part_index)
                })
                .collect();
            let [part_index] = matches.as_slice() else {
                return Err(AlethePrintError::InvalidSkolemStep {
                    id,
                    reason: format!(
                        "flattened implication disjunct {} has no unique authored antecedent complement",
                        self.surface_term(source_disjunct)
                    ),
                });
            };
            used_parts[*part_index] = true;
            self.insert_skolem_override(id, complement, antecedent_instances[*part_index].clone())?;
        }

        if !saw_consequent || used_parts.iter().any(|used| !used) {
            return Err(AlethePrintError::InvalidSkolemStep {
                id,
                reason: "flattened implication did not cover its authored antecedent/consequent"
                    .to_string(),
            });
        }
        Ok(())
    }

    fn surface_term(&self, term: TermId) -> String {
        self.term_overrides
            .and_then(|overrides| overrides.get(&term))
            .cloned()
            .unwrap_or_else(|| self.format_term(term))
    }

    fn are_boolean_complements(&self, left: TermId, right: TermId) -> bool {
        matches!(self.terms.get(left), TermData::Not(inner) if *inner == right)
            || matches!(self.terms.get(right), TermData::Not(inner) if *inner == left)
    }

    /// True when `lit` is AY's De Morgan normal form of the *logical negation*
    /// of `term`.
    ///
    /// AY's `mk_not` pushes negation all the way down (`¬(and a..) → (or ¬a..)`,
    /// `¬(or a..) → (and ¬a..)`, `¬¬x → x`) and interns commutatively (so the
    /// disjuncts/conjuncts appear in TermId-sorted order, not source order).
    /// This is exactly the spelling the clausifier stores for the
    /// `(not (and ...))` gate literal of an `and_pos` tautology, and it can be
    /// arbitrarily nested (a conjunct that is itself an `or` re-De-Morganizes).
    /// The match is order-insensitive (multiset) and recursive; interning is
    /// injective so each child pairs with exactly one negated child.
    fn is_demorgan_negation(&self, lit: TermId, term: TermId) -> bool {
        match self.terms.get(term) {
            // ¬¬x normalizes to x.
            TermData::Not(inner) => lit == *inner,
            TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
                let dual = if name == "and" { "or" } else { "and" };
                let TermData::App(Symbol::Named(lit_name), children) = self.terms.get(lit) else {
                    return false;
                };
                if lit_name != dual || children.len() != args.len() || args.is_empty() {
                    return false;
                }
                let args = args.clone();
                let children = children.clone();
                let mut used = vec![false; children.len()];
                args.iter().all(|&a| {
                    match children
                        .iter()
                        .enumerate()
                        .position(|(j, &c)| !used[j] && self.is_demorgan_negation(c, a))
                    {
                        Some(j) => {
                            used[j] = true;
                            true
                        }
                        None => false,
                    }
                })
            }
            // Atom (or an application AY does not De-Morganize): the negation is
            // a raw `(not term)`.
            _ => matches!(self.terms.get(lit), TermData::Not(inner) if *inner == term),
        }
    }

    /// Re-slot an `and_pos` tautology whose `(not (and ...))` gate literal was
    /// traced as its De Morgan surface `(or (not A1) .. (not An))`.
    ///
    /// Carcara's `and_pos` requires the first clause literal to be
    /// syntactically `(not (and A1 .. An))`, but AY's clausifier stores that
    /// gate as the De-Morganized or-term. The spec-shaped step
    /// `(cl (not (and A1 .. An)) Ak) :rule and_pos :args (k)` is the exact
    /// axiomatic tautology the annotation records; emitting it directly also
    /// makes the immediately-following resolution against the `(and ...)`
    /// assume well-formed (the or-form never was its syntactic complement).
    /// Returns `None` — leaving the default rendering — unless the traced
    /// clause is exactly `{¬(and ...)-as-or-form, Ak}`, so this is purely a
    /// printing-shape correction, never a semantic change.
    fn resugar_and_pos_not_and(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
        let ay_core::AletheRule::AndPos(i) = rule else {
            return None;
        };
        let i = *i as usize;
        let [source] = args else {
            return None;
        };
        let source = *source;
        let TermData::App(Symbol::Named(name), conjuncts) = self.terms.get(source) else {
            return None;
        };
        if name != "and" {
            return None;
        }
        let ak = *conjuncts.get(i)?;
        if clause.len() != 2 {
            return None;
        }
        let ak_str = self.format_term(ak);
        let source_str = self.format_term(source);
        let printed: [String; 2] = [self.format_term(clause[0]), self.format_term(clause[1])];
        let ak_pos = printed.iter().position(|s| *s == ak_str)?;
        let other = clause[1 - ak_pos];
        // Only fire when the non-`Ak` literal is AY's De Morgan normal form of
        // `(not source)`. When it is already the raw `(not source)` the default
        // rendering is correct, so leave it untouched (byte-stable).
        if matches!(self.terms.get(other), TermData::Not(inner) if *inner == source)
            || !self.is_demorgan_negation(other, source)
        {
            return None;
        }
        // The internal conjunct index `i` must be valid against the PRINTED
        // and-term. A surface override can re-spell `source` (e.g. re-nest a
        // flattened conjunction, or reorder commutative args), so the printed
        // arity / operand-`i` may diverge from the internal conjunct vector —
        // emitting `:args (i)` against a divergent printed shape yields a
        // wrong-index step. The fast path requires the printed `and` to split
        // into exactly the internal conjunct count with operand `i` equal to
        // `Ak`; anything else goes through the printed-nesting navigator, which
        // reads the index off the PRINTED node it actually emits.
        if let Some(printed_ops) = split_application(&source_str, "and") {
            if printed_ops.len() == conjuncts.len() && printed_ops.get(i) == Some(&ak_str) {
                return Some(format!(
                    "(step {id} (cl (not {source_str}) {ak_str}) :rule and_pos :args ({i}))"
                ));
            }
        }
        self.navigate_and_pos_gate(id, &source_str, &ak_str)
    }

    /// Derive `(cl (not ROOT) Ak)` by walking the PRINTED `and` nesting.
    ///
    /// The printed root stays byte-identical to `format_term(source)`, so the
    /// resolution step that consumes this gate against the assertion's unit
    /// clause is unaffected — only the step DECOMPOSITION changes:
    ///
    /// ```text
    /// (step tK.g0 (cl (not (and (and p q) r)) (and p q)) :rule and_pos :args (0))
    /// (step tK.g1 (cl (not (and p q)) p)                 :rule and_pos :args (0))
    /// (step tK    (cl (not (and (and p q) r)) p) :rule resolution :premises (tK.g0 tK.g1))
    /// ```
    ///
    /// Returns `None` (fail loud at the caller) when `Ak` is not a printed
    /// operand anywhere in the nesting — emitting `:args (i)` against a shape
    /// that does not hold it is exactly the wrong-index step this guards.
    /// `id` is the identifier the CONCLUSION is emitted under, and the prefix
    /// every intermediate hop is named from. It is a `Display` rather than a
    /// `ProofId` so a caller that is itself already emitting a sub-derivation
    /// (the folded-conjunction `assume` bridge) can hang the projection off its
    /// own sub-id without colliding with the step id it is repairing.
    fn navigate_and_pos_gate(
        &self,
        id: impl std::fmt::Display,
        root: &str,
        ak_str: &str,
    ) -> Option<String> {
        let nesting = PrintedNesting::build(root, "and", PRINTED_NESTING_NODE_BUDGET)?;
        if nesting.is_flat() {
            // Flat print with a mismatching index: the internal conjunct
            // vector is TermId-sorted while the surface prints the authored
            // operand order, so the wire index can differ even when `Ak` IS a
            // printed operand. Re-slot to the printed position when that
            // spelling occurs exactly once — the emitted projection is exact
            // by construction (operand `j` of the printed source is
            // byte-identical to `Ak`). Absent or duplicated spellings stay a
            // decline: do not guess.
            let operands = &nesting.operands[0];
            let mut positions = operands
                .iter()
                .enumerate()
                .filter(|(_, operand)| *operand == ak_str);
            let (index, _) = positions.next()?;
            if positions.next().is_some() {
                return None;
            }
            return Some(format!(
                "(step {id} (cl (not {root}) {ak_str}) :rule and_pos :args ({index}))"
            ));
        }
        self.charge(root.len() as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        let (node, index) = nesting.find_operand(ak_str)?;
        let path = nesting.path_to(node);
        if path.is_empty() {
            return Some(format!(
                "(step {id} (cl (not {root}) {ak_str}) :rule and_pos :args ({index}))"
            ));
        }
        let mut out = String::new();
        let mut premises = Vec::with_capacity(path.len() + 1);
        for (hop, (parent, operand_index)) in path.iter().enumerate() {
            let gate_id = format!("{id}.g{hop}");
            let parent_str = &nesting.nodes[*parent];
            let child_str = &nesting.operands[*parent][*operand_index];
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {gate_id} (cl (not {parent_str}) {child_str}) \
                     :rule and_pos :args ({operand_index}))\n"
                ),
            );
            premises.push(gate_id);
        }
        let leaf_id = format!("{id}.g{}", path.len());
        let leaf_str = &nesting.nodes[node];
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {leaf_id} (cl (not {leaf_str}) {ak_str}) :rule and_pos :args ({index}))\n"
            ),
        );
        premises.push(leaf_id);
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl (not {root}) {ak_str}) :rule resolution :premises ({}))",
                premises.join(" ")
            ),
        );
        Some(out)
    }

    /// Re-derive an `or_pos` tautology whose printed gate is a NESTED binary
    /// `or` (the mirror image of the `and_pos` defect above).
    ///
    /// carcara's `or_pos` requires the gate's TOP-LEVEL arity to equal the
    /// clause tail length; a surface override that re-nests AY's flattened
    /// n-ary `or` gives "expected 6 terms in 'or' term, got 2". Unlike
    /// `and_pos` this had NO guard at all, so a broken step shipped silently.
    ///
    /// The repair is the same shared printed-nesting walk, one `or_pos` per
    /// printed node, resolved into the traced clause:
    ///
    /// ```text
    /// (step tK.g0 (cl (not (or (or a b) c)) (or a b) c) :rule or_pos)
    /// (step tK.g1 (cl (not (or a b)) a b)               :rule or_pos)
    /// (step tK    (cl (not (or (or a b) c)) a b c) :rule resolution :premises (tK.g0 tK.g1))
    /// ```
    ///
    /// Returns `None` unless the printed leaves are exactly the traced clause
    /// tail (as a multiset of printed literals) — the guard that keeps a
    /// mis-decomposed gate off the wire.
    fn resugar_or_pos_nested(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
        if !matches!(rule, ay_core::AletheRule::OrPos(_)) {
            return None;
        }
        let [source] = args else {
            return None;
        };
        let source = *source;
        let TermData::App(Symbol::Named(name), _) = self.terms.get(source) else {
            return None;
        };
        if name != "or" || clause.len() < 2 {
            return None;
        }
        let source_str = self.format_term(source);
        // Cheap pre-check: a printed gate that is already flat AND already the
        // spec shape needs no repair, and this runs on every traced `or_pos`.
        let top = split_application(&source_str, "or")?;
        let already_flat = !top.iter().any(|o| split_application(o, "or").is_some());
        if already_flat
            && top.len() == clause.len() - 1
            && matches!(self.terms.get(clause[0]), TermData::Not(inner) if *inner == source)
        {
            return None;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        // The gate literal is whichever traced literal negates `source` —
        // either the raw `(not source)` or AY's De Morgan normal form.
        let gate_pos = clause.iter().position(|&lit| {
            matches!(self.terms.get(lit), TermData::Not(inner) if *inner == source)
                || self.is_demorgan_negation(lit, source)
        })?;
        let mut tail: Vec<String> = Vec::with_capacity(printed.len() - 1);
        for (index, literal) in printed.iter().enumerate() {
            if index != gate_pos {
                tail.push(literal.clone());
            }
        }
        let nesting = PrintedNesting::build(&source_str, "or", PRINTED_NESTING_NODE_BUDGET)?;
        self.charge(source_str.len() as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        // GUARD: the printed decomposition must reproduce exactly the traced
        // clause tail, or the emitted chain would not resolve to it. The ONLY
        // admitted difference is a leaf that is the other printed orientation
        // of its traced equality, and it is not waved through: it costs a
        // certified `eq_symmetric` / `equiv_pos2` pair below. Anything else
        // returns `None` and the caller decides between the honest hole and a
        // declined document, exactly as before.
        let (targets, bridges) = match_printed_leaves_to_tail(&nesting.leaves, &tail)?;
        let mut out = String::new();
        let mut premises = Vec::with_capacity(nesting.nodes.len() + 2 * bridges.len());
        for (node, operands) in nesting.operands.iter().enumerate() {
            let gate_id = format!("{id}.g{node}");
            let node_str = &nesting.nodes[node];
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {gate_id} (cl (not {node_str}) {}) :rule or_pos)\n",
                    operands.join(" ")
                ),
            );
            premises.push(gate_id);
        }
        if bridges.is_empty() && premises.len() == 1 {
            // Single node: the chain degenerates to the spec step itself, so
            // emit it under the traced id instead of a resolution.
            return Some(format!(
                "(step {id} (cl (not {source_str}) {}) :rule or_pos)",
                nesting.leaves.join(" ")
            ));
        }
        // One orientation bridge per divergent leaf, in the checker's own
        // calculus: `eq_symmetric` states the two equalities equivalent and
        // `equiv_pos2` turns that equivalence into the implication the final
        // resolution consumes. Nothing is claimed from a term identity the
        // checker cannot see — both steps are premise-free tautologies over the
        // printed text.
        for (index, (leaf, flipped)) in bridges.iter().enumerate() {
            let equivalence = format!("(= {leaf} {flipped})");
            self.charge(equivalence.len() as u64);
            let symmetric_id = format!("{id}.s{index}");
            let implication_id = format!("{id}.s{index}p");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!("(step {symmetric_id} (cl {equivalence}) :rule eq_symmetric)\n"),
            );
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {implication_id} (cl (not {equivalence}) (not {leaf}) {flipped}) \
                     :rule equiv_pos2)\n"
                ),
            );
            premises.push(symmetric_id);
            premises.push(implication_id);
        }
        if self.work_budget_exhausted() {
            return None;
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl (not {source_str}) {}) :rule resolution :premises ({}))",
                targets.join(" "),
                premises.join(" ")
            ),
        );
        Some(out)
    }

    /// Why the DEFAULT rendering of this `and_pos` / `or_pos` step would not
    /// check, or `None` when it is fine (or is not one of these two rules).
    ///
    /// This is the guard the `or_pos` path never had. It is deliberately
    /// evaluated only after every certified bridge has declined, and it is
    /// deliberately narrow: it fires ONLY on the two shapes measured to be
    /// rejected, so a step whose default rendering is correct is never turned
    /// into a missing proof.
    fn unrepairable_gate_reason(
        &self,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
        let [source] = args else {
            return None;
        };
        let source = *source;
        let TermData::App(Symbol::Named(name), _) = self.terms.get(source) else {
            return None;
        };
        match rule {
            ay_core::AletheRule::AndPos(_) if name == "and" => {
                // Correct by default exactly when the gate literal IS the raw
                // `(not source)`; otherwise it is the De Morgan or-form and
                // carcara rejects it as "the wrong form".
                let gate_is_raw = clause.iter().any(
                    |&lit| matches!(self.terms.get(lit), TermData::Not(inner) if *inner == source),
                );
                if gate_is_raw {
                    return None;
                }
                Some(
                    "and_pos gate literal is the De Morgan or-form and no certified \
                     printed-shape bridge applies"
                        .to_string(),
                )
            }
            ay_core::AletheRule::OrPos(_) if name == "or" => {
                let gate_is_raw = clause.iter().any(
                    |&lit| matches!(self.terms.get(lit), TermData::Not(inner) if *inner == source),
                );
                // A source term that does not PRINT as an or-term at all is
                // the shape that shipped `invalid` documents unnoticed: the
                // internal node is a genuine `or`, so AY's own strict checker
                // validates `or_pos` against the term DAG and sees nothing
                // wrong, while the surface override spells it `(not (and ..))`
                // and carcara refuses "term '(not (not (and ...)))' is of the
                // wrong form, expected '(not(or ...))'". Reading the arity off
                // a `?` here failed OPEN on exactly that case — there is no
                // arity to read, so the guard declined to guard. Every printed
                // surface that HAS a certified bridge (`=>`, the De Morgan
                // `(not (and ..))` form) has already been tried and declined by
                // the time this runs, so a non-or print is unrepairable.
                let printed = self.format_term(source);
                let Some(printed_operands) = split_application(&printed, "or") else {
                    return Some(
                        "or_pos source term does not print as an or-term and no certified \
                         printed-shape bridge applies"
                            .to_string(),
                    );
                };
                let printed_arity = printed_operands.len();
                if gate_is_raw && printed_arity == clause.len() - 1 {
                    return None;
                }
                Some(format!(
                    "or_pos printed gate arity {printed_arity} does not match the clause tail \
                     length {} and no certified printed-shape bridge applies",
                    clause.len() - 1
                ))
            }
            _ => None,
        }
    }

    /// `let`-elimination bridge for an `assume` whose surface override is a
    /// `(let ...)` term.
    ///
    /// WHY. A census of 167 non-datatype `:status unsat` instances found 36
    /// INVALID proofs; the largest class (23 instances over QF_UFLIA, QF_ALIA,
    /// QF_IDL, QF_LIA, QF_UFIDL and ALIA) is an `and_pos` step whose gate
    /// literal is printed as its De Morgan surface form. The repair for that —
    /// [`Self::resugar_and_pos_not_and`] — is blocked at its printed-shape
    /// guard whenever the assertion was authored with `let`: `source_str` is
    /// then `(let ...)`, `split_application(s, "and")` fails at its
    /// `strip_prefix("and")`, and the guard returns `None`, so the broken De
    /// Morgan step ships. Every measured instance of the class is a SINGLE
    /// `let`-rooted assertion (DTP_k2_n35_c210_s12: 2 nested lets, 40 + 16
    /// bindings; mathsat medium5/13/18/19 and piVC_f5059f likewise).
    ///
    /// The `let` cannot simply be expanded in the `assume`: carcara matches an
    /// `assume` against the problem premises with
    /// `Polyeq::new().mod_reordering(true).mod_nary(true)`, which recurses
    /// THROUGH `Term::Let` but never eliminates it — an expanded `assume`
    /// against a `let` problem is rejected outright ("could not match term to
    /// any of the original problem premises", measured).
    ///
    /// So keep the `assume` surface-exact under a derived id and hand the
    /// ORIGINAL step id to the eliminated form:
    ///
    /// ```text
    /// (assume tK.a  (let ((?v_0 e0) ..) BODY))
    /// (anchor :step tK.l :args ((:= ?v_0 e0) ..))          ; certified arm
    /// (step tK.l.t1 (cl (= BODY SUB)) :rule refl)          ;
    /// (step tK.l    (cl (= (let ..) SUB)) :rule let)       ; NO :premises
    /// (step tK.e    (cl (not (= (let ..) SUB)) (not (let ..)) SUB) :rule equiv_pos2)
    /// (step tK      (cl SUB) :rule resolution :premises (tK.e tK.l tK.a))
    /// ```
    ///
    /// The id swap is what makes this a purely local repair: every downstream
    /// step already cites `tK`, and `tK` still concludes the unit clause of the
    /// assertion — no premise reference anywhere in the document moves.
    /// `:rule let` must carry NO `:premises` (carcara drops binding pairs whose
    /// two sides are equal and then asserts the premise count, so a premise on
    /// an already-normal binding is "expected 0 premises, got 1").
    ///
    /// TARGET FORM. `SUB` is AY's own rendering of the assertion term — the
    /// form every other step in the document already prints. The alternative,
    /// substituting the surface text, was rejected by measurement: AY's
    /// internal terms are arithmetically normalized (`(<= 26 (+ x10 (- x31)))`
    /// for the authored `(>= (- x10 x31) 26)`), so a surface-substituted body
    /// would collide with every other step's spelling. When the two DO
    /// coincide the substitution is emitted as a genuine `refl`/`let`
    /// derivation (certified arm, measured `valid` end to end); otherwise the
    /// single equivalence is marked `:rule hole` (fallback arm).
    ///
    /// BE HONEST ABOUT THE COST. On the measured instances the fallback arm is
    /// what fires, and it is the FIRST hole in five of the six (only DTP
    /// already carried one), so this trades `invalid` for `holey` rather than
    /// for `valid`. That is still strictly better — an invalid proof is not a
    /// proof, a hole is a visible, countable obligation — and the hole is
    /// confined to ONE step whose obligation is exactly "this `let` eliminates
    /// to this term". Closing it needs the arithmetic/commutative
    /// normalization equalities, not more printing work.
    fn plan_let_assume_bridge(&self, term: TermId, surface: &str) -> Option<LetAssumeBridgePlan> {
        if !surface.starts_with("(let") {
            return None;
        }
        // A blown emission budget renders terms as a placeholder; bridging that
        // would bake the placeholder into the document (which is discarded
        // anyway).
        if self.work_budget_exhausted() {
            return None;
        }
        let (levels, innermost_body) = peel_printed_lets(surface)?;
        // The eliminated form: AY's structural rendering of the assertion,
        // bypassing this term's own `(let ...)` override but still honouring
        // every SUBTERM override, so the result is byte-identical to how the
        // rest of the document spells this term.
        let eliminated = self.format_term_data(self.terms.get(term));
        self.charge(eliminated.len() as u64 * 4);
        if self.work_budget_exhausted() {
            return None;
        }
        // Nothing is gained if the internal form is itself a binder: the gate
        // rules still have no shape to work with.
        if eliminated.starts_with("(let") || eliminated == surface {
            return None;
        }
        // The certified arm's textual substitution assumes every bound name is
        // bound exactly once and that SMT-LIB's PARALLEL `let` semantics never
        // bite (no level references a name it binds itself). Shadowing or a
        // self-reference would make the substitution disagree with the context
        // carcara composes, so fall back to the hole arm rather than emit a
        // `refl` the checker rejects.
        let substitution_matches =
            let_substitution::matches(&levels, &innermost_body, &eliminated, |work| {
                self.admit_emission_work(work as u64)
            });
        if self.work_budget_exhausted() {
            return None;
        }
        Some(LetAssumeBridgePlan {
            levels,
            innermost_body,
            eliminated,
            substitution_matches,
        })
    }

    fn format_let_assume_bridge(&self, id: ProofId, term: TermId, surface: &str) -> Option<String> {
        let LetAssumeBridgePlan {
            levels,
            innermost_body,
            eliminated,
            substitution_matches,
        } = self.plan_let_assume_bridge(term, surface)?;

        let mut out = String::new();
        let _ = std::fmt::Write::write_fmt(&mut out, format_args!("(assume {id}.a {surface})\n"));
        if substitution_matches {
            // Certified arm: the authored spelling survives elimination
            // unchanged, so the equivalence is a real `refl` under the `let`
            // context. Anchors nest outermost-first and only the INNERMOST
            // subproof carries the `refl`; carcara composes the contexts, so a
            // binding value mentioning an outer variable is discharged by the
            // same single step.
            let mut anchor_ids = Vec::with_capacity(levels.len());
            let mut anchor_id = format!("{id}.l");
            for (index, (bindings, _)) in levels.iter().enumerate() {
                if index > 0 {
                    anchor_id.push_str(".t1");
                }
                let args: Vec<String> = bindings
                    .iter()
                    .map(|(name, value)| format!("(:= {name} {value})"))
                    .collect();
                let _ = std::fmt::Write::write_fmt(
                    &mut out,
                    format_args!("(anchor :step {anchor_id} :args ({}))\n", args.join(" ")),
                );
                anchor_ids.push(anchor_id.clone());
            }
            let refl_id = format!("{anchor_id}.t1");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {refl_id} (cl (= {innermost_body} {eliminated})) :rule refl)\n"
                ),
            );
            // Close the subproofs innermost-first. Each `let` step concludes
            // the equivalence for the `let` term AS WRITTEN AT ITS LEVEL.
            for (index, level_id) in anchor_ids.iter().enumerate().rev() {
                let level_surface = if index == 0 {
                    surface
                } else {
                    levels[index - 1].1.as_str()
                };
                let _ = std::fmt::Write::write_fmt(
                    &mut out,
                    format_args!(
                        "(step {level_id} (cl (= {level_surface} {eliminated})) :rule let)\n"
                    ),
                );
            }
            // Valid only in pinned Carcara's plain invocation: the report
            // says so (`CarcaraSurface::WithoutLetExpansion`).
            dialect::note_problem_let_rule();
        } else {
            // Fallback arm: one visible, countable trust hole for the
            // let-elimination equivalence itself.
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!("(step {id}.l (cl (= {surface} {eliminated})) :rule hole)\n"),
            );
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id}.e (cl (not (= {surface} {eliminated})) (not {surface}) {eliminated}) \
                 :rule equiv_pos2)\n\
                 (step {id} (cl {eliminated}) :rule resolution :premises ({id}.e {id}.l {id}.a))"
            ),
        );
        self.let_bridge_renderings
            .borrow_mut()
            .insert(term, eliminated);
        Some(out)
    }

    fn surface_complement_matches(&self, disjunct: TermId, expected: &str) -> bool {
        if let TermData::Not(inner) = self.terms.get(disjunct) {
            if self.surface_term(*inner) == expected {
                return true;
            }
        }
        // Integer/real order negation is often normalized to the opposite
        // relation rather than represented as a raw `not` node (`not (<= a
        // b)` becomes `(< b a)`). Match that exact surface dual as well; the
        // enclosing strictly checked or_neg step still pins the actual
        // internal Boolean complement.
        if surface_strings_are_complements(&self.surface_term(disjunct), expected) {
            return true;
        }
        self.term_overrides.is_some_and(|overrides| {
            overrides.iter().any(|(&candidate, surface)| {
                surface == expected && self.are_boolean_complements(disjunct, candidate)
            })
        })
    }

    /// Re-spell every rendering that names a resugared Skolem witness by its
    /// internal symbol, so one witness `TermId` has ONE spelling at every
    /// print site: the `choice` term.
    ///
    /// ## The defect this closes (the eighth false green, 2026-09-12)
    ///
    /// The producer's surface-override table is rendered BEFORE this printer
    /// exists, through `format_term_alethe_with_overrides` over a printer that
    /// has had no Skolem preparation. A `forall_inst` instance built there
    /// from an authored quantifier body under `binder := witness`
    /// (`format_forall_instance_surface`) therefore carries the witness's
    /// internal name — `(> (f sk!z_11_12) sk!z_11_12)` — while this printer
    /// renders the witness's own `TermId` as its `choice` term at every other
    /// site, including that very step's `:args`. Same `TermId`, two spellings;
    /// `write_term_into` consults the producer's table before the structural
    /// rendering, so the instance shipped raw and pinned carcara 1.1.0 refused
    /// the document at the parser: `identifier 'sk!z_11_12' is not defined`.
    /// Every internal signal was green, because every internal check compares
    /// `TermId`s and both spellings are one `TermId`.
    ///
    /// ## Why substituting the token is exact
    ///
    /// A witness symbol is globally fresh (`TermStore::mark_skolem_symbol` at
    /// the single mint site), so no authored text can mention it: every raw
    /// occurrence in a rendering is the image of a binder under the
    /// substitution that produced that rendering, and replacing the token by
    /// the witness's `choice` term yields exactly the text the printer would
    /// have produced from the pattern itself — the operation
    /// [`Self::register_substituted_surface_overrides`] already performs for
    /// the Skolemized body's own subterms, extended to every other rendering.
    /// `substitute_smt_symbol`'s tokenizer never touches string literals,
    /// quoted-symbol contents or longer identifiers.
    ///
    /// Order matters and is taken from mint order (`TermId`): a later
    /// witness's `choice` body may mention an earlier witness (a Skolemized
    /// `exists` under an instantiated `forall`), never the reverse, so each
    /// witness's own text is finalized against the witnesses before it, then
    /// every other printer rendering and finally the producer's table are
    /// re-spelled against the finalized set. A producer entry the printer has
    /// already re-rendered, or one confined to unused `assume` leaves, is left
    /// alone.
    ///
    /// A witness with no `choice` (one the preamble will `define-fun`) keeps
    /// its name everywhere; only resugared witnesses are re-spelled.
    ///
    /// Returns the producer entries copied into this printer's table, which
    /// `plan_confined_forall_instances` may still confine.
    fn respell_renderings_naming_witnesses(&self) -> HashSet<TermId> {
        let mut witnesses: Vec<(TermId, String)> = self
            .skolem_overrides
            .borrow()
            .keys()
            .filter_map(|&term| match self.terms.get(term) {
                TermData::Var(name, _) if self.is_skolem_witness_name(name) => {
                    Some((term, quote_symbol(name)))
                }
                _ => None,
            })
            .collect();
        if witnesses.is_empty() {
            return HashSet::default();
        }
        witnesses.sort_by_key(|(term, _)| *term);
        let mut spelling: HashMap<String, String> = HashMap::default();
        for (term, token) in &witnesses {
            let Some(choice) = self.skolem_overrides.borrow().get(term).cloned() else {
                continue;
            };
            let choice = respell_symbol_tokens(&choice, &spelling).unwrap_or(choice);
            self.skolem_overrides
                .borrow_mut()
                .insert(*term, choice.clone());
            spelling.insert(token.clone(), choice);
        }
        let respelled: Vec<(TermId, String)> = self
            .skolem_overrides
            .borrow()
            .iter()
            .filter_map(|(term, text)| {
                respell_symbol_tokens(text, &spelling).map(|text| (*term, text))
            })
            .collect();
        let mut mine = self.skolem_overrides.borrow_mut();
        for (term, text) in respelled {
            mine.insert(term, text);
        }
        let mut copied = HashSet::default();
        let Some(overrides) = self.term_overrides else {
            return copied;
        };
        let assume_only = self.assume_only_override_terms.borrow();
        for (term, text) in overrides {
            if mine.contains_key(term) || assume_only.contains(term) {
                continue;
            }
            if let Some(text) = respell_symbol_tokens(text, &spelling) {
                mine.insert(*term, text);
                copied.insert(*term);
            }
        }
        copied
    }

    fn insert_skolem_override(
        &self,
        id: ProofId,
        term: TermId,
        rendering: String,
    ) -> Result<(), AlethePrintError> {
        let mut overrides = self.skolem_overrides.borrow_mut();
        if let Some(prior) = overrides.get(&term) {
            if prior != &rendering {
                return Err(AlethePrintError::InvalidSkolemStep {
                    id,
                    reason: format!(
                        "term {term} acquired incompatible choice renderings `{prior}` and `{rendering}`"
                    ),
                });
            }
            return Ok(());
        }
        overrides.insert(term, rendering);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn register_substituted_surface_overrides(
        &self,
        id: ProofId,
        pattern: TermId,
        instance: TermId,
        binder: &str,
        surface_binder: &str,
        witness: TermId,
        choice: &str,
    ) -> Result<(), AlethePrintError> {
        if let Some(surface) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&pattern))
        {
            self.insert_skolem_override(
                id,
                instance,
                substitute_smt_symbol(surface, surface_binder, choice),
            )?;
        }
        match self.terms.get(pattern) {
            TermData::Var(name, _) if name == binder => {
                if instance != witness {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "binder did not align with the recorded witness".to_string(),
                    });
                }
            }
            TermData::Var(..) | TermData::Const(..) => {
                if pattern != instance {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "non-binder leaf changed during substitution".to_string(),
                    });
                }
            }
            TermData::Not(inner) => {
                let TermData::Not(actual) = self.terms.get(instance) else {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "negation shape changed during substitution".to_string(),
                    });
                };
                self.register_substituted_surface_overrides(
                    id,
                    *inner,
                    *actual,
                    binder,
                    surface_binder,
                    witness,
                    choice,
                )?;
            }
            TermData::Ite(c, t, e) => {
                let TermData::Ite(ac, at, ae) = self.terms.get(instance) else {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "ite shape changed during substitution".to_string(),
                    });
                };
                for (expected, actual) in [(*c, *ac), (*t, *at), (*e, *ae)] {
                    self.register_substituted_surface_overrides(
                        id,
                        expected,
                        actual,
                        binder,
                        surface_binder,
                        witness,
                        choice,
                    )?;
                }
            }
            TermData::App(symbol, args) => {
                let TermData::App(actual_symbol, actual_args) = self.terms.get(instance) else {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "application shape changed during substitution".to_string(),
                    });
                };
                if symbol != actual_symbol || args.len() != actual_args.len() {
                    return Err(AlethePrintError::InvalidSkolemStep {
                        id,
                        reason: "application symbol/arity changed during substitution".to_string(),
                    });
                }
                for (&expected, &actual) in args.iter().zip(actual_args) {
                    self.register_substituted_surface_overrides(
                        id,
                        expected,
                        actual,
                        binder,
                        surface_binder,
                        witness,
                        choice,
                    )?;
                }
            }
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
                return Err(AlethePrintError::InvalidSkolemStep {
                    id,
                    reason: "nested binder/let is outside certified Skolem printer scope"
                        .to_string(),
                });
            }
            _ => {
                return Err(AlethePrintError::InvalidSkolemStep {
                    id,
                    reason: "unsupported term variant in Skolem substitution".to_string(),
                });
            }
        }
        Ok(())
    }

    pub(crate) fn is_skolem_witness_name(&self, name: &str) -> bool {
        self.skolem_witness_names.borrow().contains(name)
    }

    /// Alethe `define-fun` lines for the Skolem CONSTANTS among `wanted`, in
    /// mint order, paired with the names they cover.
    ///
    /// ## Why a definition and not a declaration
    ///
    /// A Skolem constant is not a fresh opaque symbol the proof may assume
    /// things about — it denotes `εx. B`, and `∃x. B ⟺ B[x := εx. B]` is an
    /// equivalence. Declaring it instead states something strictly stronger
    /// than the problem: nothing licenses a FRESH constant satisfying `B`.
    ///
    /// It also has to be a definition for a blunter reason, MEASURED on carcara
    /// 1.1.0: its proof grammar (`Parser::parse_proof`) admits only `assume`,
    /// `step`, `anchor` and `define-fun`. A `(declare-fun ...)` anywhere in the
    /// document — first line or not — is `parser error: unexpected token:
    /// 'declare-fun'`, so every proof AY has ever emitted with a non-empty
    /// declaration preamble was rejected before a single rule was checked.
    /// `(define-fun c () S (choice ...))` parses, and carcara expands it, so
    /// the checked document is exactly the one with the choice term inlined at
    /// every occurrence — without paying that term's size per occurrence.
    ///
    /// ## Fail-closed
    ///
    /// A definition is emitted ONLY when every free variable of the choice body
    /// is resolvable in the document: declared by the problem, or defined by an
    /// EARLIER line here. A witness that fails the test is simply not covered,
    /// and the caller then DECLINES the whole export — there is no declaration
    /// fallback, because `(declare-fun ...)` is exactly what makes a document
    /// unparseable (see [`AlethePrintError::UndeclarableProofSymbols`]).
    ///
    /// Free APPLICATION symbols are not checked here: AY's declaration
    /// collector does not see those either, so a proof-only function symbol is
    /// a pre-existing defect of a different class, and this guard neither fixes
    /// nor worsens it.
    ///
    /// ## No two witnesses may share a body (the COLLAPSE guard)
    ///
    /// `define-fun` is a MACRO: carcara expands each body inline, so two
    /// symbols defined by the same body become the SAME term. MEASURED on
    /// carcara 1.1.0 with `(define-fun sk1 () U (choice ((x U)) true))` and
    /// `(define-fun sk2 () U (choice ((x U)) true))`, the step
    /// `(step t2 (cl (= sk1 sk2)) :rule refl)` checks and the document is
    /// `valid` — two DISTINCT Skolem constants proved equal. With distinct
    /// bodies the same step is rejected (`reflexivity failed`), so the
    /// identification is caused by the shared body and nothing else.
    ///
    /// Equality is judged up to renaming of the choice BINDER, because carcara
    /// compares terms modulo alpha: MEASURED, `(choice ((x U)) true)` and
    /// `(choice ((y U)) true)` also collapse. Any body text that repeats after
    /// that normalization disqualifies EVERY witness sharing it — the export
    /// then declines rather than shipping an identification AY cannot justify.
    ///
    /// Residual, measured and deliberately left open: carcara also identifies
    /// bodies that differ only in an INNER binder's name
    /// (`(choice ((x U)) (forall ((z U)) (q x z)))` vs the same with `w` for
    /// `z` checks `valid`). Normalizing only the outer binder does not catch
    /// that shape. It needs alpha-normalization of the whole term, which the
    /// printer cannot do against an immutable [`TermStore`]; the bodies here
    /// are quantifier bodies taken verbatim from the problem, so two witnesses
    /// reaching it would have to come from source existentials identical but
    /// for an inner bound name.
    pub(crate) fn skolem_choice_definitions(
        &self,
        wanted: &HashSet<String>,
        problem_symbols: &HashSet<String>,
    ) -> (Vec<String>, HashSet<String>) {
        // Phase 1 — render every candidate body ONCE, in mint order. The
        // rendering is needed twice (to detect a shared body and to emit the
        // line) and `format_term` is the expensive part of this method.
        let mut candidates: Vec<(&String, &ay_core::SkolemChoice, String)> = Vec::new();
        // Bodies that occur in the document but are NOT emission candidates.
        // They still collapse against an emitted definition, so the census in
        // phase 2 must see them (see `census_only` below).
        let mut census_only: Vec<(&ay_core::SkolemChoice, String)> = Vec::new();
        for (witness, choice) in self.terms.skolem_choices() {
            let TermData::Var(name, _) = self.terms.get(witness) else {
                continue;
            };
            if !wanted.contains(name) {
                continue;
            }
            // A witness the printer already resugared to an inline `choice`
            // must not ALSO be defined here: it never reaches the preamble.
            //
            // But it MUST still be counted by the collapse guard. `define-fun`
            // is a macro, so an emitted definition whose body is textually the
            // inline term identifies the two. MEASURED on carcara 1.1.0: with
            // `(define-fun sk!i_other () Int (choice ((i Int)) (not (P i))))`
            // alongside a step spelling that same choice term inline,
            // `(step t9 (cl (= (choice ((i Int)) (not (P i))) sk!i_other))
            //  :rule refl)` PASSES the rule check -- a distinct witness proved
            // equal to an inline occurrence. Skipping these before the census
            // (which is what this `continue` used to do) made the guard blind
            // to exactly that shape.
            if self.is_skolem_witness_name(name) {
                census_only.push((choice, self.format_term(choice.body)));
                continue;
            }
            // Capture guard: the binder is printed by NAME, so a document
            // symbol spelled the same way would be captured by it. AY's binder
            // renaming makes this vanishingly rare; withholding the definition
            // costs nothing that was working.
            if problem_symbols.contains(&choice.binder) {
                continue;
            }
            candidates.push((name, choice, self.format_term(choice.body)));
        }

        // Phase 2 — the COLLAPSE guard. Normalize the binder away so that
        // alpha-variants share a key, then disqualify every key seen twice.
        let mut key_counts: HashMap<String, usize> = HashMap::default();
        let census = candidates
            .iter()
            .map(|(_, choice, body)| (*choice, body))
            .chain(census_only.iter().map(|(choice, body)| (*choice, body)));
        for (choice, body) in census {
            let key = format!(
                "{}|{}",
                choice.sort,
                substitute_smt_symbol(body, &choice.binder, CHOICE_BINDER_NORMAL_FORM)
            );
            *key_counts.entry(key).or_insert(0) += 1;
        }

        // Phase 3 — emit, in mint order, so a body may name an earlier witness.
        let mut lines = Vec::new();
        let mut covered: HashSet<String> = HashSet::default();
        for (name, choice, body) in &candidates {
            if covered.contains(*name) {
                continue;
            }
            let key = format!(
                "{}|{}",
                choice.sort,
                substitute_smt_symbol(body, &choice.binder, CHOICE_BINDER_NORMAL_FORM)
            );
            if key_counts.get(&key).is_some_and(|count| *count > 1) {
                continue;
            }
            // A binder spelled like an EARLIER definition would capture it.
            if covered.contains(&choice.binder) {
                continue;
            }
            let body_symbols = crate::variables::free_var_names(self.terms, [choice.body]);
            let resolvable = body_symbols.iter().all(|symbol| {
                symbol == &choice.binder
                    || symbol != *name
                        && (problem_symbols.contains(symbol) || covered.contains(symbol))
            });
            if !resolvable {
                continue;
            }
            lines.push(format!(
                "(define-fun {} () {} (choice (({} {})) {body}))",
                quote_symbol(name),
                choice.sort,
                quote_symbol(&choice.binder),
                choice.sort,
            ));
            covered.insert((*name).clone());
        }
        // Rendering the preamble is the FIRST formatting the document does, so
        // it would otherwise seed `format_cache` with entries computed before
        // `format_step` installs its `let`-bridge renderings. Drop them: the
        // preamble must be invisible to step rendering, exactly as
        // `prepare_proof` ends by dropping its own. (The cache is empty on
        // entry, so this discards only what this method just added.)
        self.format_cache.borrow_mut().clear();
        (lines, covered)
    }

    /// Record `amount` units of rendering work (saturating).
    fn charge(&self, amount: u64) {
        self.work.set(self.work.get().saturating_add(amount));
    }
    /// Admit before the bounded operation allocates or scans. Exhaustion and
    /// caller refusal cannot be erased by a speculative bridge rollback.
    fn admit_emission_work(&self, amount: u64) -> bool {
        if self.check_emission_progress(0).is_err() || self.work_budget_exhausted() {
            return false;
        }
        self.charge(amount);
        !self.work_budget_exhausted()
    }

    pub(crate) fn check_emission_progress(
        &self,
        steps_rendered: u32,
    ) -> Result<(), AlethePrintError> {
        if self.printed_clause_bytes.is_poisoned() {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id: ProofId(steps_rendered),
                reason: "printed allocation accounting poisoned".into(),
            });
        }
        if !self.emission_progress.poll() {
            return Err(AlethePrintError::EmissionStopped { steps_rendered });
        }
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(steps_rendered));
        }
        Ok(())
    }
    /// Return the actual accumulated rendering work.
    pub(crate) fn work_used(&self) -> u64 {
        self.work.get()
    }
    /// Whether work is exhausted or the retained caller has stopped emission.
    pub(crate) fn work_budget_exhausted(&self) -> bool {
        !self.emission_progress.poll() || self.work_budget.is_some_and(|b| self.work.get() > b)
    }
    /// Typed exhaustion error for the caller's per-step check.
    pub(crate) fn work_budget_error(&self, steps_rendered: u32) -> AlethePrintError {
        if self.emission_progress.refused() {
            return AlethePrintError::EmissionStopped { steps_rendered };
        }
        AlethePrintError::EmissionBudgetExhausted {
            budget: self.work_budget.unwrap_or(0),
            steps_rendered,
        }
    }

    /// The already-printed plain `assume` that carries the equality
    /// `(= left right)` (or `(= right left)`, reported as `reversed`),
    /// either as its whole conclusion or as one top-level conjunct of a
    /// flat `(and ...)` conclusion.
    ///
    /// WHY THIS IS AUTHORITY AND NOT A GUESS. The returned id names an
    /// `assume` command that is already in the document, and carcara matches
    /// every `assume` against the ORIGINAL problem's assertions before it
    /// checks a single rule. So the clause this returns is a hypothesis of the
    /// query itself: citing it as a premise adds no assumption the document
    /// did not already carry, and an id whose text does not match a problem
    /// assertion is rejected by the checker at the `assume`, loudly, rather
    /// than silently licensing a step. A conjunct of an assumed conjunction is
    /// the same hypothesis one ordinary `and_pos` projection away.
    ///
    /// The comparison is on the EXACT emitted text, which is the only thing an
    /// external checker sees, and only plain `assume` rows are recorded (see
    /// [`Self::assume_printed`]). Ordering is safe by construction: entries
    /// appear as `format_step` walks the proof, so every candidate was printed
    /// above the step that reads this.
    ///
    /// A whole-assume match wins over a conjunct match; within each kind the
    /// SMALLEST id (then the smallest conjunct index) is returned, so the
    /// choice is deterministic across runs and hash orders.
    fn printed_assume_equality(&self, left: &str, right: &str) -> Option<PrintedAssumeEquality> {
        let assumes = self.assume_printed.borrow();
        if assumes.is_empty() {
            return None;
        }
        // One scan of the recorded assume texts for the whole-assume match,
        // and at most one bounded top-level split per text for the conjunct
        // match. Charge both before they run (#A2b).
        let scanned: u64 = assumes.values().map(|text| text.len() as u64).sum();
        self.charge(scanned.saturating_mul(2));
        if self.work_budget_exhausted() {
            return None;
        }
        let forward = format!("(= {left} {right})");
        let reverse = format!("(= {right} {left})");
        let orientation = |text: &str| {
            if text == forward {
                Some(false)
            } else if text == reverse {
                Some(true)
            } else {
                None
            }
        };
        let mut whole: Option<(ProofId, bool)> = None;
        let mut conjunct: Option<(ProofId, AssumedConjunctKind, bool)> = None;
        for (id, text) in assumes.iter() {
            if let Some(reversed) = orientation(text) {
                if whole.is_none_or(|(current, _)| id.0 < current.0) {
                    whole = Some((*id, reversed));
                }
                continue;
            }
            let Ok(operands) =
                split_alethe_application_bounded(text, "and", text.len(), text.len())
            else {
                continue;
            };
            if operands.len() < 2 {
                continue;
            }
            let direct = operands.iter().enumerate().find_map(|(index, operand)| {
                orientation(operand).map(|r| (AssumedConjunctKind::Direct(index), r))
            });
            // An authored `(=> P E)` whose antecedent `P` is itself a sibling
            // operand carries `E` one `implies_pos` away.
            let found = direct.or_else(|| {
                operands
                    .iter()
                    .enumerate()
                    .find_map(|(implication, operand)| {
                        let (antecedent_text, consequent) = split_binary_implies(operand)?;
                        let reversed = orientation(&consequent)?;
                        let antecedent = operands
                            .iter()
                            .enumerate()
                            .find(|&(index, other)| {
                                index != implication && *other == antecedent_text
                            })?
                            .0;
                        Some((
                            AssumedConjunctKind::Implied {
                                implication,
                                implication_text: (*operand).to_string(),
                                antecedent,
                                antecedent_text,
                            },
                            reversed,
                        ))
                    })
            });
            let Some((kind, reversed)) = found else {
                continue;
            };
            if conjunct
                .as_ref()
                .is_none_or(|(current, _, _)| id.0 < current.0)
            {
                conjunct = Some((*id, kind, reversed));
            }
        }
        if let Some((assume, reversed)) = whole {
            return Some(PrintedAssumeEquality {
                assume,
                reversed,
                conjunct: None,
            });
        }
        let (assume, kind, reversed) = conjunct?;
        let gate = format!("(not {})", assumes.get(&assume)?);
        Some(PrintedAssumeEquality {
            assume,
            reversed,
            conjunct: Some(AssumedConjunctEquality { gate, kind }),
        })
    }

    /// Format a proof step as an Alethe command.
    ///
    /// Returns `Err(AlethePrintError)` when the step cannot be rendered as a
    /// verifiable rule — including `LraFarkas` / `LiaGeneric` theory lemmas
    /// missing their `FarkasAnnotation` (#8821) and array-extensionality lemmas
    /// whose internal witness provenance has no stock Alethe translation. The
    /// caller is responsible for deciding how to handle the error: tests /
    /// `try_export_alethe` surface it directly; the backwards-compatible
    /// `export_alethe` path emits a clearly-marked unverifiable document and
    /// logs to stderr rather than silently writing `:rule trust`.
    pub(crate) fn format_step(
        &self,
        step: &ProofStep,
        id: ProofId,
    ) -> Result<String, AlethePrintError> {
        let _scratch_scope = printed_resolution::ScratchScope::enter(
            &self.printed_replay_scratch,
            printed_command::MAX_STEP_BYTES,
            &self.printed_clause_bytes,
        );
        let rendered = match self.format_step_text(step, id) {
            Ok(rendered) => rendered,
            // Only where the caller asked for it: the honest `hole` over the
            // step's own clause (`refused_surface_hole`).
            Err(error) => self
                .refused_surface_step_hole(step, id, &error)
                .ok_or(error)?,
        };
        // An exhausted budget is reported AS exhaustion before any judgement
        // reads the rendering. Past exhaustion `write_term_into` renders
        // every term as `@a2b_emission_budget_exhausted`, and the document is
        // discarded at the next step boundary whatever happens here — but the
        // three judgements below and the ledger `record_printed_conclusion`
        // fills would otherwise read placeholder text as if it were the
        // document, and a judgement over placeholders reports a divergence
        // that does not exist (MEASURED: `judge_printed_resolution` on
        // iso_icl641 refused a valid step as "the printed premises do not
        // eliminate the printed resolution pivot"). The `Step` arm checks the
        // same condition for its own candidate ordering; this is the
        // chokepoint every variant passes through.
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        // A witness the printer resugared to a `choice` term is, on the
        // printer's CLAIM, not a free symbol of the document — which is why
        // the exporter neither defines nor declares it. Check the claim on
        // the bytes: a rendering channel that still spells the witness raw
        // ships an identifier no checker can resolve, and no rule name can
        // make that document parseable, so the export declines. After
        // `respell_renderings_naming_witnesses` this cannot fire; it is what
        // turns "cannot" from an argument into a check.
        {
            let witnesses = self.skolem_witness_names.borrow();
            if !witnesses.is_empty() {
                if let Some(name) = first_symbol_token_in(&rendered, &witnesses) {
                    return Err(AlethePrintError::ResugaredWitnessPrintedRaw {
                        id,
                        name: name.clone(),
                    });
                }
            }
        }
        // Every `la_generic` this step ships is judged over the bytes it
        // ships, whatever channel spelled them. See
        // `judge_printed_la_generic`.
        let rendered = self.judge_printed_la_generic(step, id, rendered)?;
        let rendered = self.judge_printed_la_disequality(step, id, rendered)?;
        // Every `comp_simplify` / `evaluate` it ships is judged as pinned
        // Carcara reads the printed terms (`printed_simplify`).
        let rendered = self.judge_printed_simplify(step, id, rendered)?;
        // Every `:rule or` / `ite1` / `ite2` / `not_ite1` / `not_ite2` this step
        // ships is judged against the PRINTED conclusion of its premise.
        let rendered = self.judge_printed_premise_rules(step, id, rendered)?;
        // Record what this id actually put on the wire BEFORE any later step
        // cites it as a premise. `judge_printed_resolution` reads exactly this
        // and nothing else, so the judgement is over the shipped bytes.
        self.record_printed_conclusion(id, &rendered);
        // Recording also reads/hashes actual wire bytes. A refusal or work
        // exhaustion there must be observed before this text leaves the API.
        self.check_emission_progress(id.0)?;
        Ok(rendered)
    }

    /// Judge every `:rule la_generic` command in one rendered step over the
    /// exact literal text and `:args` it ships, replaying the pinned
    /// checker's own procedure ([`la_generic_surface::printed_la_generic_holds`]).
    ///
    /// ONE chokepoint, on the bytes, for all fourteen sites that print
    /// `la_generic`. Every earlier admission of that rule — `promoted_wire_rule`,
    /// `la_generic_farkas_lowering_supported`, `int_bounds_tautology_lowering_supported`,
    /// `arith_eq_implies_bound_lowering_supported`, `lia_divisibility_lowering_supported`
    /// and the rest of the `wire_term_overrides` readers — classifies the
    /// PRODUCER's override table and is blind by construction to this
    /// printer's own channels (`skolem_overrides`, `let_bridge_renderings`):
    /// a Skolemized authored body whose literal is a simplification of what
    /// it spells (`(ite (= z z) z 0)` for `z`) reaches the wire in its authored
    /// spelling through `register_substituted_surface_overrides`, the table
    /// says "identity", and the step ships as `la_generic` over rows the
    /// checker cannot cancel. That was the ninth false green (2026-09-13,
    /// pinned carcara: `final disequality is not contradictory`). The table
    /// readers still decide WHICH rule to attempt; this decides whether the
    /// text they produced instantiates it.
    ///
    /// `poly_simp` commands are replayed the same way
    /// ([`la_generic_surface::printed_poly_simp_holds`]): it is the other
    /// rule the arithmetic table readers promote to.
    ///
    /// A refusal declines the whole step to the honest `hole` over its own
    /// clause — every multi-command lowering binds `id` last, with exactly
    /// that clause, and its sub-ids are cited by nothing else — or declines
    /// the export at an `assume`, which has no hole. Never a different rule
    /// name, never a bridge AY did not derive.
    fn judge_printed_la_generic(
        &self,
        step: &ProofStep,
        id: ProofId,
        rendered: String,
    ) -> Result<String, AlethePrintError> {
        // A cheap pre-filter, and ONLY a pre-filter: a step whose bytes never
        // mention either rule name cannot claim either rule, so there is
        // nothing to judge and nothing to read. Everything below reads
        // COMMANDS, never rendered text.
        let mentions_arith_rule = rendered.contains("la_generic") || rendered.contains("poly_simp");
        if !mentions_arith_rule {
            return Ok(rendered);
        }
        use la_generic_surface::PrintedArithCommand as Command;
        let has_la_generic;
        let definitions = std::cell::OnceCell::new(); // the step's define-funs, read lazily
        let refused = match la_generic_surface::printed_arith_commands(&rendered) {
            Some(commands) => {
                has_la_generic = commands.iter().any(|c| matches!(c, Command::LaGeneric(..)));
                commands.iter().find_map(|command| match command {
                    la_generic_surface::PrintedArithCommand::LaGeneric(command) => {
                        (!la_generic_surface::printed_la_generic_holds(
                            &command.literals,
                            &command.args,
                        ))
                        .then(|| command.name.to_string())
                    }
                    // The `poly_simp` replay is the pinned build's polynomial
                    // normalizer, which is COARSER than nothing: it refuses
                    // only a difference it fully decides (`Some(false)`), so
                    // text it cannot expand keeps the promotion's decision.
                    la_generic_surface::PrintedArithCommand::PolySimp { name, left, right } => {
                        la_generic_surface::printed_poly_simp_refused(
                            left,
                            right,
                            &rendered,
                            &definitions,
                        )
                        .then(|| (*name).to_string())
                    }
                    la_generic_surface::PrintedArithCommand::Unreadable { name } => {
                        Some(name.map_or_else(|| id.to_string(), ToString::to_string))
                    }
                })
            }
            None => {
                // The rendered text is not a sequence of commands this reader
                // can split. Decide on TOKENS, not on `contains`: a quoted
                // symbol or a string literal that happens to spell the rule is
                // an operand, not a claim.
                has_la_generic = false;
                la_generic_surface::rendered_rule_field_names_arith(&rendered)
                    .then(|| id.to_string())
            }
        };
        let clause: Option<&[TermId]> = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::FiniteFieldLinear { clause, .. }
            | ProofStep::NraSos { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause),
            _ => None,
        };
        if ay_core::misc_cli_flags().debug_cert {
            let surface =
                clause.is_some_and(|clause| self.clause_reaches_rendering_channel(clause));
            ay_core::safe_eprintln!(
                "c !! {} surface at {id}: override={} verdict={}",
                if has_la_generic {
                    "la_generic"
                } else {
                    "poly_simp"
                },
                if surface { "yes" } else { "no" },
                match &refused {
                    Some(name) => format!("refused({name})"),
                    None => "holds".to_string(),
                }
            );
        }
        let Some(refused_name) = refused else {
            return Ok(rendered);
        };
        let Some(clause) = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: format!(
                    "printed arithmetic step `{refused_name}` is not an instance of its rule over the text it ships"
                ),
            });
        };
        Ok(format!(
            "(step {id} {} :rule {})",
            self.format_clause(clause),
            ay_core::UNPROVED_STEP_RULE
        ))
    }

    /// The rendering table a wire-rule judgement must classify: every entry
    /// `write_term_into` would consult, with the same precedence — the
    /// producer's (assume-planned) table, then the `let` bridge, then the
    /// Skolem `choice` table. `None` when no channel is installed.
    ///
    /// The eighth shape's siblings were judged over `wire_term_overrides`
    /// alone: a Skolemized authored body whose literal the store had
    /// simplified reached the wire through `skolem_overrides`, the producer's
    /// table called it an identity, and `la_generic` shipped over rows the
    /// checker cannot cancel. Cached against the sizes of the three tables —
    /// `skolem_overrides` is complete after `prepare_proof`, and the other
    /// two only grow — and rebuilt when any of them does.
    ///
    /// Read by the three judgements that have NO printed-text replay of
    /// their own — `trans_step_surface_is_supported`,
    /// `evaluate_step_lowering_supported` and the `la_disequality` triangle
    /// (`arith_eq_triangle_lowering_supported`) — so they classify what the
    /// document prints. DELIBERATELY NOT read by the five arithmetic
    /// promotions (`promoted_wire_rule`, the `poly_simp`, integer-bounds,
    /// equality-bound and divisibility lowerings): those are judged over the
    /// printed bytes by `judge_printed_la_generic`, which replays the
    /// checker exactly, while this table's classifier is coarser than the
    /// checker — MEASURED: over the effective table it reads the `(+ z 0)`
    /// spelling of a witness as `Divergent` and holes a `la_generic` the
    /// checker accepts (its `LinearComb` folds `(+ c 0)`), which the
    /// `skolemla` gate row exists to refuse.
    fn judgement_overrides(&self) -> std::cell::Ref<'_, Option<HashMap<TermId, String>>> {
        let fingerprint = (
            self.wire_term_overrides
                .borrow()
                .as_ref()
                .map_or(0, HashMap::len),
            self.let_bridge_renderings.borrow().len(),
            self.skolem_overrides.borrow().len(),
        );
        {
            let cache = self.judgement_overrides.borrow();
            if cache.as_ref().is_some_and(|(seen, _)| *seen == fingerprint) {
                return std::cell::Ref::map(cache, |cache| {
                    &cache.as_ref().expect("checked above").1
                });
            }
        }
        let (let_bridge, skolem) = (
            self.let_bridge_renderings.borrow(),
            self.skolem_overrides.borrow(),
        );
        let mut table: HashMap<TermId, String> = HashMap::default();
        let assume_only = self.assume_only_override_terms.borrow();
        if let Some(wire) = self.wire_term_overrides.borrow().as_ref() {
            for (term, text) in wire {
                if !assume_only.contains(term) {
                    table.insert(*term, text.clone());
                }
            }
        }
        for (term, text) in let_bridge.iter().chain(skolem.iter()) {
            table.insert(*term, text.clone());
        }
        // Charged like any rendering work (#A2b); past exhaustion the
        // document is discarded and the counter must stand still.
        if !self.work_budget_exhausted() {
            let bytes: usize = table.values().map(String::len).sum();
            self.charge(bytes as u64);
        }
        let table = (!table.is_empty()).then_some(table);
        *self.judgement_overrides.borrow_mut() = Some((fingerprint, table));
        std::cell::Ref::map(self.judgement_overrides.borrow(), |cache| {
            &cache.as_ref().expect("just stored").1
        })
    }

    /// Whether any literal of `clause`, or any subterm the printer would
    /// recurse into, is spelled by a rendering channel rather than
    /// structurally — the producer's table, the `let` bridge, or this
    /// printer's Skolem `choice` table. A census predicate, not a judgement.
    fn clause_reaches_rendering_channel(&self, clause: &[TermId]) -> bool {
        let skolem = self.skolem_overrides.borrow();
        let let_bridge = self.let_bridge_renderings.borrow();
        let assume_only = self.assume_only_override_terms.borrow();
        let mut stack: Vec<TermId> = clause.to_vec();
        let mut seen: HashSet<TermId> = HashSet::default();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if skolem.contains_key(&term)
                || let_bridge.contains_key(&term)
                || (!assume_only.contains(&term)
                    && self
                        .term_overrides
                        .is_some_and(|overrides| overrides.contains_key(&term)))
            {
                return true;
            }
            stack.extend(self.terms.children(term));
        }
        false
    }

    fn format_step_text(&self, step: &ProofStep, id: ProofId) -> Result<String, AlethePrintError> {
        // Normal export initializes this in `prepare_proof`; isolated
        // step-formatting helpers enter here directly. Both paths must apply
        // the same pre-clone admission before consulting wire-rule predicates.
        self.initialize_wire_term_overrides()?;
        match step {
            ProofStep::Assume(term_id) => {
                self.assume_terms.borrow_mut().insert(id, *term_id);
                // FIRST: every other bridge re-spells the assumed term, while
                // this one restores shells the problem wrote and elaboration
                // deleted. A leaf that keeps the wrong shell count is not a
                // premise of the query at all, whatever else is spelled right.
                if let Some(bridge) = self.format_negation_shell_assume_bridge(id, *term_id)? {
                    return Ok(bridge);
                }
                if let Some(bridge) = self.format_equivalent_authored_assume_bridge(id, *term_id)? {
                    return Ok(bridge);
                }
                if let Some(bridge) = self.format_folded_and_assume_bridge(id, *term_id) {
                    return Ok(bridge);
                }
                let term_str = self.format_term(*term_id);
                // A `let`-rooted assertion assumed MORE THAN ONCE. The first
                // assume's bridge installs the eliminated body in
                // `let_bridge_renderings` — deliberately, so every downstream
                // STEP prints the eliminated form — and `format_term` therefore
                // hands this leaf that body instead of the authored `(let ...)`
                // spelling. The bridge below then sees no `let`, declines, and
                // the second assume ships the eliminated text, which carcara
                // cannot match against the `(let ...)` PROBLEM premise:
                //
                //   [ERROR] checking failed on step 't135' with rule 'assume':
                //   could not match term to any of the original problem premises
                //
                // MEASURED on QF_UF QG-classification `gensys_icl483`,
                // `gensys_icl798` and `gensys_icl448`, where assertion 0 is
                // assumed twice: `t0` carries the full bridge and `t135` does
                // not. carcara's assume matching recurses THROUGH `Term::Let`
                // but never eliminates it, so an eliminated `assume` against a
                // `let` premise is refused and the whole document is `invalid`.
                //
                // Re-read the AUTHORED spelling for this leaf — only when an
                // earlier bridge is what shadowed it — so every occurrence of
                // the same assertion carries the same bridge under its own ids.
                let shadowed_authored_surface = self
                    .let_bridge_renderings
                    .borrow()
                    .contains_key(term_id)
                    .then(|| {
                        self.term_overrides
                            .and_then(|overrides| overrides.get(term_id))
                            .cloned()
                    })
                    .flatten();
                let bridge_surface = shadowed_authored_surface
                    .as_deref()
                    .unwrap_or(term_str.as_str());
                if let Some(bridge) = self.format_let_assume_bridge(id, *term_id, bridge_surface) {
                    return Ok(bridge);
                }
                // Only the plain path records: this id concludes exactly
                // `term_str`, which is what a later consumer may cite.
                self.assume_printed
                    .borrow_mut()
                    .insert(id, term_str.clone());
                Ok(format!("(assume {id} {term_str})"))
            }
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => self.format_resolution_step(id, clause, *pivot, *clause1, *clause2),
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                kind,
                lia,
            } => self.format_theory_lemma(id, theory, clause, farkas.as_ref(), kind, lia.as_ref()),
            ProofStep::NraSos {
                clause,
                certificate,
            } => self.format_nra_sos_step(id, clause, certificate),
            ProofStep::FiniteFieldLinear {
                clause,
                multipliers,
            } => {
                if clause.is_empty()
                    || clause.len() != multipliers.len()
                    || u32::try_from(clause.len()).is_err()
                    || clause.iter().any(|term| {
                        term.index() >= self.terms.len() || self.terms.sort(*term) != &Sort::Bool
                    })
                {
                    return Err(AlethePrintError::UnsupportedStep { id });
                }
                let clause = self.format_clause(clause);
                if self.work_budget_exhausted() {
                    return Err(self.work_budget_error(id.0));
                }
                // Spell the fixed refusal explicitly so the wire-rule inventory
                // probes the emitted rule instead of counting an opaque placeholder.
                Ok(format!("; {id} native finite-field certificate retained in AY bundle; no Alethe lowering\n(step {id} {clause} :rule hole)"))
            }
            ProofStep::Step {
                rule: ay_core::AletheRule::Skolem,
                clause,
                premises,
                args,
            } => self.format_certified_skolem_step(id, clause, premises, args),
            // Extensionality diff-witness INTRODUCTION. This is AY-internal
            // provenance (it lets AY's own checker certify the Skolemized
            // extensionality clause); it is not an Alethe inference and has no
            // conclusion, so it renders as a COMMENT. Emitting `(step tN (cl)
            // ...)` here would hand an external checker a bogus derivation of
            // the empty clause.
            //
            // NOTE (corrected 2026-08-04): this used to say the witness symbol
            // "is still declared in the `(declare-fun ...)` preamble, so the
            // document stays complete". That is now FALSE in both halves. No
            // declaration command is emitted anywhere -- carcara's proof
            // grammar rejects one outright -- and `__ay_ext_diff!NN` has no
            // choice-term provenance, so it cannot be rendered as a
            // `define-fun` either. It is precisely what makes the two
            // `QF_ALIA/ios` instances DECLINE. The document does not stay
            // complete; the export refuses instead, which is the intended
            // fail-closed behaviour.
            ProofStep::Step {
                rule: ay_core::AletheRule::ArrayExtDiffIntro,
                clause,
                premises,
                args,
            } => {
                crate::checker::validate_ext_diff_intro_for_printer(
                    self.terms, id, clause, premises, args,
                )
                .map_err(|err| AlethePrintError::InvalidSkolemStep {
                    id,
                    reason: err.to_string(),
                })?;
                let rendered: Vec<String> = args.iter().map(|&a| self.format_term(a)).collect();
                Ok(format!(
                    "; {id} array_ext_diff_intro witness {} for arrays {} {}",
                    rendered[0], rendered[1], rendered[2]
                ))
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                if matches!(rule, ay_core::AletheRule::QntNegExists)
                    && premises.is_empty()
                    && args.is_empty()
                {
                    if let Some(chain) = self.format_qnt_neg_exists_chain(id, clause) {
                        return Ok(chain);
                    }
                }
                let rendered = self.format_generic_step(id, rule, clause, premises, args);
                // A specialized bridge may finish assembling a candidate on
                // the exact operation that crosses the budget. The current
                // step has not been returned or written yet, so exhaustion
                // dominates that candidate and counts only prior step ids.
                if self.work_budget_exhausted() {
                    Err(self.work_budget_error(id.0))
                } else {
                    rendered
                }
            }
            ProofStep::Anchor {
                end_step,
                variables,
            } => Ok(Self::format_anchor(*end_step, variables)),
            // `ProofStep` is #[non_exhaustive]: a future variant added in
            // ay-core must surface as a typed error, not a runtime panic.
            _ => Err(AlethePrintError::UnsupportedStep { id }),
        }
    }

    fn format_certified_skolem_step(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        crate::checker::quantifier::validate_sko_forall(
            self.terms,
            id,
            clause,
            premises.len(),
            args,
        )
        .map_err(|err| AlethePrintError::InvalidSkolemStep {
            id,
            reason: err.to_string(),
        })?;
        let [equality] = clause else {
            unreachable!("validated Skolem clause")
        };
        let TermData::App(Symbol::Named(_), equality_args) = self.terms.get(*equality) else {
            unreachable!("validated Skolem equality")
        };
        let (quantified, instance) = (equality_args[0], equality_args[1]);
        // Both validator-admitted readings: `sko_forall` (forall source) and
        // `sko_ex` (registered positive exists source).
        let (bindings, body, rule) = match self.terms.get(quantified) {
            TermData::Forall(bindings, body, _) => (bindings, body, "sko_forall"),
            TermData::Exists(bindings, body, _) => (bindings, body, "sko_ex"),
            _ => unreachable!("validated Skolem source"),
        };
        let [(binder, binder_sort)] = bindings.as_slice() else {
            unreachable!("validated Skolem binder")
        };
        let [witness] = args else {
            unreachable!("validated Skolem witness")
        };
        let Some(choice) = self.skolem_overrides.borrow().get(witness).cloned() else {
            return Err(AlethePrintError::InvalidSkolemStep {
                id,
                reason: "printer was not prepared with the witness choice mapping".to_string(),
            });
        };
        let (binder, body) = self.skolem_surface_binder_and_body(
            quantified,
            *body,
            binder,
            if rule == "sko_ex" { "exists" } else { "forall" },
        );
        let quantified = self.format_term(quantified);
        let instance = self.format_term(instance);
        // Judge the three commands over the text they ship, the way the
        // pinned checker will read them: the anchor must bind the printed
        // quantifier's own binder to `(choice ((x S)) (not BODY))`, the `refl`
        // must equate that BODY with its substitution image, and the step
        // must equate the printed quantifier with the same image. Every
        // piece was rendered through a channel the term store cannot see;
        // when they disagree the honest floor is the hole, never a step
        // named for a rule the text does not instantiate.
        let sort = format_sort_alethe(binder_sort);
        let printed = quantifier_surface::PrintedSkolemStep {
            rule,
            quantified: &quantified,
            binder: &binder,
            sort: &sort,
            choice: &choice,
            body: &body,
            instance: &instance,
        };
        // A step with a recorded constant bridge is judged by the bridge's
        // own judgement and never falls through to the `refl` form
        // (`skolem_step_form` says why and its tests pin it).
        let bridge = self.constant_skolem_bridges.borrow().get(&id).cloned();
        match constant_skolem_bridge::skolem_step_form(id, &printed, bridge.as_ref()) {
            constant_skolem_bridge::SkolemStepForm::Bridged(bridged) => Ok(bridged),
            constant_skolem_bridge::SkolemStepForm::Refl => Ok(format!(
                "(anchor :step {id} :args ((:= ({binder} {sort}) {choice})))\n\
                 (step {id}.t1 (cl (= {body} {instance})) :rule refl)\n\
                 (step {id} (cl (= {quantified} {instance})) :rule {rule})"
            )),
            constant_skolem_bridge::SkolemStepForm::Hole => Ok(format!(
                "(step {id} (cl (= {quantified} {instance})) :rule {})",
                ay_core::UNPROVED_STEP_RULE
            )),
        }
    }

    /// Print a resolution whose internal pivot remains a syntactic Boolean
    /// complement after surface rewriting. Arithmetic-order normalization can
    /// make the two printed premise literals semantic duals instead (`(< b
    /// a)` versus `(<= a b)`). In that case add the exact `la_generic`
    /// excluded-middle clause between them and resolve in an order Carcara can
    /// check syntactically.
    fn format_resolution_step(
        &self,
        id: ProofId,
        clause: &[TermId],
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
    ) -> Result<String, AlethePrintError> {
        // A binary `(distinct a b)` literal is AY's internal spelling of
        // `(not (= a b))`, but Carcara's resolution treats it as an opaque
        // atom, so a resolution that cancels `(distinct a b)` against an
        // equality `(= a b)` / `(= b a)` reports "pivot was not eliminated".
        // Bridge it honestly with `distinct_elim` (+ `symm` for the swapped
        // argument order) before falling through to the generic rendering.
        if let Some(text) = self.distinct_eq_resolution_bridge(id, clause, clause1, clause2) {
            return Ok(text);
        }
        if self.surface_resolution_needs_distinct_bridge(clause, Some(pivot), clause1, clause2) {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason:
                    "a printed distinct/equality pivot cannot be bridged to the authored operands"
                        .to_string(),
            });
        }
        if let Some(text) = self.symmetric_equality_resolution_bridge(id, clause, clause1, clause2)
        {
            return Ok(text);
        }
        if let Some((left, right)) =
            self.surface_order_resolution_pair(clause, pivot, clause1, clause2)
        {
            return Ok(format!(
                "(step {id}.ord (cl (not {left}) (not {right})) :rule la_generic :args (1 1))\n\
                 (step {id} {} :rule resolution :premises ({clause1} {id}.ord {clause2}))",
                self.format_clause(clause)
            ));
        }

        // LAST, after every specialized bridge has declined: replay the step
        // over the text the premises actually printed. Every guard above this
        // one reads the term store; this one reads the document — the
        // conclusion is rendered ONCE, here, and the judgement reads the
        // bytes the step below ships.
        let clause_str = self.format_clause(clause);
        if let Some(text) =
            self.judge_printed_resolution(id, clause, &clause_str, &[clause1, clause2])?
        {
            return Ok(text);
        }

        // Omit :args — Carcara infers an ordinary syntactic pivot from the
        // premises.
        Ok(format!(
            "(step {id} {clause_str} :rule resolution :premises ({clause1} {clause2}))"
        ))
    }

    /// Whether an internally complementary pivot prints as `distinct` versus
    /// equality but the exact surface-operand bridge could not be built.
    fn surface_resolution_needs_distinct_bridge(
        &self,
        clause: &[TermId],
        pivot: Option<TermId>,
        clause1: ProofId,
        clause2: ProofId,
    ) -> bool {
        let clauses = self.proof_clauses.borrow();
        let (Some(c1), Some(c2)) = (clauses.get(&clause1), clauses.get(&clause2)) else {
            return false;
        };
        let expected: HashSet<TermId> = clause.iter().copied().collect();
        for (left_index, &left) in c1.iter().enumerate() {
            for (right_index, &right) in c2.iter().enumerate() {
                if !self.are_boolean_complements(left, right)
                    || pivot.is_some_and(|pivot| {
                        !(left == pivot
                            || right == pivot
                            || self.are_boolean_complements(left, pivot)
                            || self.are_boolean_complements(right, pivot))
                    })
                {
                    continue;
                }
                let mut resolvent = HashSet::default();
                resolvent.extend(
                    c1.iter()
                        .enumerate()
                        .filter_map(|(index, &literal)| (index != left_index).then_some(literal)),
                );
                resolvent.extend(
                    c2.iter()
                        .enumerate()
                        .filter_map(|(index, &literal)| (index != right_index).then_some(literal)),
                );
                if resolvent != expected {
                    continue;
                }

                let left = self.format_term(left);
                let right = self.format_term(right);
                if (split_application(&left, "distinct").is_some()
                    && split_application(&right, "=").is_some())
                    || (split_application(&right, "distinct").is_some()
                        && split_application(&left, "=").is_some())
                {
                    return true;
                }
            }
        }
        false
    }

    /// Honestly rebuild a resolution that cancels a binary `(distinct a b)`
    /// literal against an equality unit clause.
    ///
    /// AY normalizes binary `(distinct a b)` to the internal term
    /// `(not (= a b))` (with the equality's args interned in TermId order) and
    /// re-spells it `(distinct a b)` on print via a surface override so the
    /// `assume` matches the input assertion. Internally the two premise
    /// literals are exact `Not` complements, but Carcara sees the *printed*
    /// `(distinct a b)` versus `(= a b)` / `(= b a)` and reports "pivot was not
    /// eliminated". Bridge over the *printed* forms:
    ///
    ///   {id}.de (cl (= (distinct a b) (not (= a b))))   distinct_elim
    ///   {id}.e1 (cl (not (distinct a b)) (not (= a b)))  equiv1
    ///   {id}.n  (cl <rest of distinct clause> (not (= a b)))  resolution
    ///   {id}.s  (cl (= a b))                              symm   (swapped only)
    ///   {id}    <clause>                                  resolution
    ///
    /// The equality-bearing premise must be a unit so the derived resolvent is
    /// exactly `rest(distinct clause)` and the optional `symm` is well-formed.
    /// Returns `None` unless that resolvent equals `clause`, so this is a
    /// printing-shape correction, never a semantic change.
    fn distinct_eq_resolution_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause1: ProofId,
        clause2: ProofId,
    ) -> Option<String> {
        let clauses = self.proof_clauses.borrow();
        let c1 = clauses.get(&clause1)?.clone();
        let c2 = clauses.get(&clause2)?.clone();
        drop(clauses);
        // The sorted printed conclusion, rendered only once a candidate
        // `(distinct a b)` / `(= a b)` pair needs comparing against it. Every
        // binary resolution passes through this bridge and almost none has a
        // unit equality premise; rendering the conclusion up front charged
        // the emission work budget a full extra copy of every resolution's
        // clause for nothing (MEASURED 2026-09-19 on iso_icl641: 2.05
        // charges per recovered step where the judgement's own double charge
        // had already been removed).
        let mut expected: Option<Vec<String>> = None;

        // `dclause`/`dpid` holds the printed `(distinct a b)` literal; the
        // other premise is the equality unit clause. Try both assignments.
        for (dclause, dpid, eq_clause, eqpid) in
            [(&c1, clause1, &c2, clause2), (&c2, clause2, &c1, clause1)]
        {
            if eq_clause.len() != 1 {
                continue;
            }
            let eq_str = self.format_term(eq_clause[0]);
            let Some(eq_ops) = split_application(&eq_str, "=") else {
                continue;
            };
            let [x, y] = eq_ops.as_slice() else {
                continue;
            };
            for (didx, &dlit) in dclause.iter().enumerate() {
                let d_str = self.format_term(dlit);
                let Some(d_ops) = split_application(&d_str, "distinct") else {
                    continue;
                };
                let [a, b] = d_ops.as_slice() else {
                    continue;
                };
                let swapped = if x == a && y == b {
                    false
                } else if x == b && y == a {
                    true
                } else {
                    continue;
                };
                let mut rest: Vec<String> = dclause
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != didx)
                    .map(|(_, &literal)| self.format_term(literal))
                    .collect();
                let mut rest_sorted = rest.clone();
                rest_sorted.sort();
                let expected = expected.get_or_insert_with(|| {
                    let mut printed: Vec<String> =
                        clause.iter().map(|&l| self.format_term(l)).collect();
                    printed.sort();
                    printed
                });
                if rest_sorted != *expected {
                    continue;
                }
                let dist = format!("(distinct {a} {b})");
                let eq = format!("(= {a} {b})");
                let rest_str = if rest.is_empty() {
                    String::new()
                } else {
                    format!("{} ", std::mem::take(&mut rest).join(" "))
                };
                let mut out = format!(
                    "(step {id}.de (cl (= {dist} (not {eq}))) :rule distinct_elim)\n\
                     (step {id}.e1 (cl (not {dist}) (not {eq})) :rule equiv1 :premises ({id}.de))\n\
                     (step {id}.n (cl {rest_str}(not {eq})) :rule resolution :premises ({dpid} {id}.e1))\n"
                );
                let eq_premise = if swapped {
                    let _ = std::fmt::Write::write_fmt(
                        &mut out,
                        format_args!("(step {id}.s (cl {eq}) :rule symm :premises ({eqpid}))\n"),
                    );
                    format!("{id}.s")
                } else {
                    eqpid.to_string()
                };
                let _ = std::fmt::Write::write_fmt(
                    &mut out,
                    format_args!(
                        "(step {id} {} :rule resolution :premises ({id}.n {eq_premise}))",
                        self.format_clause(clause)
                    ),
                );
                return Some(out);
            }
        }
        None
    }

    fn surface_order_resolution_pair(
        &self,
        clause: &[TermId],
        pivot: TermId,
        clause1: ProofId,
        clause2: ProofId,
    ) -> Option<(String, String)> {
        let clauses = self.proof_clauses.borrow();
        let left_clause = clauses.get(&clause1)?;
        let right_clause = clauses.get(&clause2)?;
        let expected: HashSet<TermId> = clause.iter().copied().collect();
        let mut match_pair = None;

        for (left_index, &left_lit) in left_clause.iter().enumerate() {
            for (right_index, &right_lit) in right_clause.iter().enumerate() {
                if !self.are_boolean_complements(left_lit, right_lit)
                    || !(left_lit == pivot
                        || right_lit == pivot
                        || self.are_boolean_complements(left_lit, pivot)
                        || self.are_boolean_complements(right_lit, pivot))
                {
                    continue;
                }
                let mut resolvent = HashSet::default();
                resolvent.extend(
                    left_clause
                        .iter()
                        .enumerate()
                        .filter_map(|(index, &lit)| (index != left_index).then_some(lit)),
                );
                resolvent.extend(
                    right_clause
                        .iter()
                        .enumerate()
                        .filter_map(|(index, &lit)| (index != right_index).then_some(lit)),
                );
                if resolvent != expected {
                    continue;
                }

                let left = self.format_term(left_lit);
                let right = self.format_term(right_lit);
                let surface_dual = surface_order_negation(&left).is_some_and(|dual| dual == right)
                    || surface_order_negation(&right).is_some_and(|dual| dual == left);
                if !surface_dual {
                    continue;
                }
                let candidate = (left, right);
                if match_pair.as_ref().is_some_and(|prior| prior != &candidate) {
                    return None;
                }
                match_pair = Some(candidate);
            }
        }
        match_pair
    }

    fn format_theory_lemma(
        &self,
        id: ProofId,
        theory: &str,
        clause: &[TermId],
        farkas: Option<&ay_core::FarkasAnnotation>,
        kind: &ay_core::TheoryLemmaKind,
        lia: Option<&ay_core::LiaAnnotation>,
    ) -> Result<String, AlethePrintError> {
        // The complete certificate, or (fail closed) the honest hole below.
        if matches!(kind, ay_core::TheoryLemmaKind::BvUremBound) {
            if let Some(text) = self.format_urem_bound(id, clause) {
                return Ok(text);
            }
            if self.emission_progress.refused() || self.work_budget_exhausted() {
                return Err(self.work_budget_error(id.0));
            }
        }
        if matches!(kind, ay_core::TheoryLemmaKind::BvMulOverflowDivision) {
            if let Some(text) = self.format_mul_overflow_division(id, clause) {
                return Ok(text);
            }
            // A declined shape keeps the honest hole; an original-owner
            // refusal must not become a fresh fallback rendering attempt.
            if self.emission_progress.refused() {
                return Err(self.work_budget_error(id.0));
            }
        }
        if matches!(kind, ay_core::TheoryLemmaKind::GroundEqualitySubstitution) {
            if let Some(text) = self.format_ground_substitution(id, clause) {
                return Ok(text);
            }
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArithEqTriangle) {
            let wire_overrides = self.judgement_overrides();
            if crate::arith_eq_triangle_lowering_supported(
                self.terms,
                clause,
                wire_overrides.as_ref(),
            ) {
                return self.format_arith_eq_triangle(id, clause);
            }
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "arithmetic equality triangle changed under surface rewriting".to_string(),
            });
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArithEqImpliesBound) {
            let wire_overrides = self.wire_term_overrides.borrow();
            if crate::arith_eq_implies_bound_lowering_supported(
                self.terms,
                clause,
                wire_overrides.as_ref(),
            ) {
                return self.format_arith_eq_implies_bound(id, clause);
            }
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "arithmetic equality implication changed under surface rewriting"
                    .to_string(),
            });
        }
        if matches!(kind, ay_core::TheoryLemmaKind::IntBoundsTautology) {
            let wire_overrides = self.wire_term_overrides.borrow();
            if crate::int_bounds_tautology_lowering_supported(
                self.terms,
                clause,
                wire_overrides.as_ref(),
            ) {
                return self.format_unit_farkas_clause(id, clause, "integer bounds tautology");
            }
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "integer bounds tautology changed under surface rewriting".to_string(),
            });
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology) && farkas.is_none() {
            let endpoints = {
                let overrides = self.judgement_overrides();
                crate::arith_order_split_lowering(self.terms, clause, overrides.as_ref())
            };
            if let Some((a, b, lt, eq, bound)) = endpoints {
                let (a, b) = (self.format_term(a), self.format_term(b));
                let equality = self.format_term(clause[eq]);
                let less = self.format_term(clause[lt]);
                let not_bound = self.format_term(clause[bound]);
                let conclusion = self.format_clause(clause);
                return Ok(format!(
                    "(step {id}.split (cl (or {equality} {not_bound} (not (<= {b} {a})))) :rule la_disequality)\n\
                     (step {id}.flat (cl {equality} {not_bound} (not (<= {b} {a}))) :rule or :premises ({id}.split))\n\
                     (step {id}.order (cl (<= {b} {a}) {less}) :rule la_generic :args (1 1))\n\
                     (step {id}.joined (cl {equality} {not_bound} {less}) :rule resolution :premises ({id}.flat {id}.order))\n\
                     (step {id} {conclusion} :rule reordering :premises ({id}.joined))"
                ));
            }
        }
        // `ArithClauseTautology` is a broad native rule, while
        // `LiaGeneric`/`LinearIdentity` is a unit positive equality that
        // Carcara cannot check as `la_generic`. Their one-equality polynomial
        // identity subset has a standard, premise-free Alethe rule:
        // `poly_simp`. Re-run the narrower checker on the exact internal clause
        // before selecting that wire spelling; all other arithmetic
        // tautologies retain their honest unsupported-rule fallback.
        if matches!(
            kind,
            ay_core::TheoryLemmaKind::ArithClauseTautology | ay_core::TheoryLemmaKind::LiaGeneric
        ) {
            let supported = {
                let mut budget = self.poly_simp_promotion_budget.borrow_mut();
                let wire_overrides = self.wire_term_overrides.borrow();
                crate::theory_lemma_poly_simp_lowering_supported(
                    self.terms,
                    kind,
                    lia,
                    clause,
                    wire_overrides.as_ref(),
                    &mut budget,
                )
            };
            if supported {
                let clause_str = self.format_clause(clause);
                return Ok(format!("(step {id} {clause_str} :rule poly_simp)"));
            }
        }
        let complement = self.format_bv_structural_arithmetic(
            id,
            clause,
            kind,
            &mut self.poly_simp_promotion_budget.borrow_mut(),
        );
        if let Some(text) = complement {
            return Ok(text);
        }
        if let Some(text) = self.format_arith_disequality_split(id, kind, clause) {
            return Ok(text);
        }
        // A render inside a solve does not lower again what that solve's
        // screen declined (`bv_support_memo/within_solve.rs`).
        let declined = matches!(
            kind,
            ay_core::TheoryLemmaKind::BvBitBlast | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
        ) && self.support_declined(kind, clause);
        // AY replays a bit-blast/LRAT refutation, while Alethe's checked
        // `aci_simp` covers exactly binary `bvand` operand swaps. Lower only
        // that shape; every other BvBitBlast lemma keeps the honest hole.
        if !declined && matches!(kind, ay_core::TheoryLemmaKind::BvBitBlast) {
            if let Some(text) = self.format_binary_bvand_aci_simp(id, clause) {
                return Ok(text);
            }
        }
        // Checked Carcara lowerings re-derive their exact clause and surface
        // shapes from the terms alone, so they are also valid for the
        // gate-annotated subset and a pure-BV `BvLiaTautology`. (A native
        // arithmetic tautology reaches the same lowering through
        // `format_bv_structural_arithmetic`, under the proof-wide attempt cap.)
        if !declined
            && matches!(
                kind,
                ay_core::TheoryLemmaKind::BvBitBlast
                    | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
                    | ay_core::TheoryLemmaKind::BvLiaTautology
            )
        {
            if let Some(text) = self.format_checked_bv_bitblast_lowering(id, clause) {
                return Ok(text);
            }
        }
        // Lower the internal conservative-extension certificate to Carcara's
        // `arrays_ext` shape (fresh witness rendered as the exact epsilon
        // term). Anything outside that exactly-reconstructible subset still
        // fails closed: `TheoryLemmaKind::ArrayExtensionality.alethe_rule()` is
        // the unknown rule name `extensionality`, which must never be emitted.
        if matches!(kind, ay_core::TheoryLemmaKind::ArrayExtensionality) {
            return self.format_array_extensionality(id, clause);
        }
        if let ay_core::TheoryLemmaKind::ArraySelectStore { index_eq } = kind {
            return self.format_array_select_store(id, clause, *index_eq);
        }
        // Lower an internally checked read-over-write CHAIN to Carcara's
        // `arrays_idx`/`arrays_row`/`cong`/`trans`. `None` means the clause is
        // outside the exactly-reconstructible subset: fall through to the
        // faithful (but externally uncheckable) `read_over_write_chain` rule
        // name rather than emit anything the derivation cannot justify.
        if matches!(kind, ay_core::TheoryLemmaKind::ArrayRowChain) {
            if let Some(text) = self
                .format_array_row_chain(id, clause)
                .or_else(|| self.format_shadowed_stores(id, clause))
            {
                return Ok(text);
            }
        }
        // Lower an internally checked n-ary store PERMUTATION to Carcara's
        // `arrays_ext`/`arrays_row`/`arrays_idx`/`cong`/`trans`. `None` means
        // the clause is outside the exactly-reconstructible subset: fall
        // through to the honest `hole` wire rather than emit a derivation the
        // printed clause does not license.
        if matches!(kind, ay_core::TheoryLemmaKind::ArrayStorePermutation) {
            if let Some(text) = self.format_array_store_permutation(id, clause) {
                return Ok(text);
            }
        }
        // Lower an internally checked three-literal guarded ROW expansion to
        // `arrays_row`/`arrays_idx`/`cong`/`trans`; `None` (the `ite`
        // spellings, a constant-array fill, a non-compositional surface)
        // keeps the honest `hole` below. See `guarded_row_expansion`.
        if matches!(kind, ay_core::TheoryLemmaKind::IteBranchProjection) {
            if let Some(text) = self.format_ite_branch_projection(id, clause) {
                return Ok(text);
            }
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArrayGuardedRowExpansion) {
            if let Some(text) = self.format_array_guarded_row_expansion(id, clause) {
                return Ok(text);
            }
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArrayDefaultConst) {
            return Err(AlethePrintError::InvalidArrayStep {
                id,
                reason: "the pinned Alethe checker has no sound rule for the non-standard array `default` operator; the exact schema is certified only by AY's native strict checker"
                    .to_string(),
            });
        }
        if kind.alethe_rule() == "eq_congruent" {
            match self.surface_eq_congruent_bridge(id, clause, &[], &[]) {
                Ok(Some(text)) => return Ok(text),
                Ok(None) => {}
                Err(reason) => {
                    return Err(AlethePrintError::InvalidCongruenceStep { id, reason });
                }
            }
            // Every `eq_congruent` the bridge above declines is judged over
            // its printed text before it reaches the wire. The bridge reads
            // the term DAG and answers `Ok(None)` below two literals, which is
            // how the lazy-EUF lane's OR-packed unit `(cl (or ¬e_1 .. e))`
            // shipped under its rule name — carcara's floor is two literals,
            // so that document was `invalid` (QF_UF `iso_brn925` `t1892`,
            // 2026-09-20). The unit now spells as the rule over its printed
            // disjuncts, resolved back to its exact text; a flat clause that
            // is an exact instance renders byte-identically; anything the
            // replay refuses is the honest hole. See `eq_congruent`.
            if let Some(text) = self.format_eq_congruent_or_hole(id, clause) {
                return Ok(text);
            }
        }

        // Integer lattice theorems (a unit Divisibility disequality, an
        // all-equality `IntGuardedSplitGap`) lower to checked `la_generic`
        // steps; see `equality_lattice`. `None` keeps the honest hole below.
        let wire_overrides = self.wire_term_overrides.borrow();
        if let Some(text) =
            self.format_lia_lattice(id, clause, kind, lia, wire_overrides.as_ref())?
        {
            return Ok(text);
        }

        let clause_str = self.format_clause(clause);
        let wire_rule =
            crate::promoted_wire_rule(self.terms, kind, clause, farkas, wire_overrides.as_ref());
        if let Some(text) = self.format_promoted_lia_evaluation(id, clause, &clause_str, wire_rule)
        {
            return Ok(text);
        }
        // Only where the wire rule is ALREADY the honest hole: a two-literal
        // clause stating one atom under two authored spellings is not an
        // `la_generic` instance in any calculus (carcara cannot negate a
        // positive equality into one linear row), so `promoted_wire_rule` has
        // answered `UNPROVED_STEP_RULE` and this can displace nothing the
        // checker accepts.
        if wire_rule == ay_core::UNPROVED_STEP_RULE {
            if let Some(text) = self.format_respelled_atom_implication(id, clause) {
                return Ok(text);
            }
        }
        if let Some(farkas) = farkas {
            return Ok(self.format_farkas_theory_lemma(id, clause, &clause_str, wire_rule, farkas));
        }

        // #8821 fail-loud: la_generic / lia_generic REQUIRE :args (Farkas
        // coefficients). Without them carcara rejects the step, and prior
        // to #8821 this path silently rewrote the rule to `trust` — which
        // the #8759 terminal-trust detector did NOT flag (the underlying
        // ProofStep::TheoryLemma.kind was still LraFarkas/LiaGeneric, so
        // `is_trust()` returned false). We now refuse to emit an
        // unverifiable rule and surface the error to the caller.
        if matches!(
            kind,
            ay_core::TheoryLemmaKind::LraFarkas | ay_core::TheoryLemmaKind::LiaGeneric
        ) {
            return Err(AlethePrintError::MissingFarkasAnnotation {
                theory: theory.to_string(),
                rule: kind.alethe_rule(),
                kind: AlethePrintError::kind_name(kind),
                step: id.0,
            });
        }

        if let Some(text) = self.format_eq_transitive_or_hole(id, clause, kind) {
            return Ok(text);
        }
        if kind.alethe_rule() == "eq_congruent_pred"
            && !self.eq_congruent_pred_prints_spec_valid(clause)
        {
            return Ok(self.eq_congruent_pred_chain_or_hole(id, clause));
        }
        // A selector over a constructor has a rule only in Clean's vendored
        // Carcara (`dt_project`); pinned Carcara has no datatype rule. Only
        // the Clean dialect prints it, and the render discloses it
        // (`CleanOnlySpelling::DatatypeSelectorProject`). The pinned dialect,
        // and any clause the lowering's IR or printed-text judgement refuses,
        // falls through to the honest hole below. See `dt_project.rs`.
        if matches!(kind, ay_core::TheoryLemmaKind::DatatypeSelectorProject) {
            if let Some(text) = dialect::attempt(|| self.format_dt_project(id, clause)) {
                return Ok(text);
            }
        }

        // Non-arithmetic kinds fall through to their own rule name, mapped to
        // the WIRE name. Every lowering above this point that found a real
        // Alethe inference has already returned; what is left is a theory
        // lemma AY can state but not justify in the checker's calculus —
        // `TheoryLemmaKind::Generic` (internally `"trust"`), `dt_project` in
        // the pinned dialect or where its Clean lowering above declines, the
        // array/string/FP kinds with no Alethe counterpart. Those print as
        // `hole`: the checker accepts the document as *holey* and the step is
        // machine-readable as unproved, where an unknown rule name would make
        // the whole proof `invalid`. Datatype distinctness belongs in that set:
        // its former `dt_distinct` -> `dt_clash` alias was reverted after the
        // installed carcara 1.1.0 answered `unknown rule`, making every such
        // document invalid where `hole` keeps the unsupported step explicit.
        //
        // The #8759 terminal-trust detector is unaffected — it walks the proof
        // IR and reads `kind.is_trust()` / `AletheRule::Hole`, both of which
        // still flag this step, not the printed text.
        //
        // Last chance before the hole: a handful of these clauses ARE a real
        // Alethe axiom, just filed under a coarse AY kind. Recover the real
        // rule from the clause shape so the step is genuinely checked.
        // Theory-lemma steps are printed without premises, so promotion to a
        // real boolean-constant axiom is available here.
        let wire = Self::wire_rule_for_printed_step(kind.alethe_wire_rule(), &clause_str, true);
        // ... and a name the checker only accepts WITH premises/`:args` is not
        // an option here either, because the step below carries neither. The
        // lowerings above this point that DO print premises (`bitblast_*`
        // sequences, the ground-eval derivations) have already returned.
        let wire = Self::wire_rule_for_bare_step(wire);
        if wire == ay_core::UNPROVED_STEP_RULE {
            if let Some(text) = Self::lower_ground_bv_disequality(id, &clause_str) {
                return Ok(text);
            }
            if let Some(text) = self.lower_closed_boolean_clause(id, &clause_str) {
                return Ok(text);
            }
            if let Some(text) = self.format_bv_complete_blast_clause(id, clause, kind) {
                return Ok(text);
            }
            if let Some(text) = self.lower_permuted_or_pos(id, &clause_str) {
                return Ok(text);
            }
            // A validated bit-blast lemma decided by its closed atoms.
            if let Some(text) = self.lower_closed_guard_lemma(kind, id, &clause_str) {
                return Ok(text);
            }
            // WHICH internal kind was downgraded to the wire hole is the one
            // fact a holey-certificate triage needs, and the document does not
            // carry it (the honest wire name is `hole` for every such kind).
            // Same typed-carrier disclosure as the checker's decline prints.
            if ay_core::misc_cli_flags().debug_cert {
                ay_core::safe_eprintln!(
                    "c !! wire downgrade at {id:?}: kind {kind:?} prints as hole"
                );
                if matches!(kind, ay_core::TheoryLemmaKind::IteBranchProjection) {
                    if clause_str.len() <= 4096 {
                        ay_core::safe_eprintln!("c !! ITE projection printed clause: {clause_str}");
                    } else {
                        ay_core::safe_eprintln!(
                            "c !! ITE projection printed clause omitted: {} bytes",
                            clause_str.len()
                        );
                    }
                }
            }
        }
        Ok(format!("(step {id} {clause_str} :rule {wire})"))
    }

    /// Lower the flat arithmetic equality-adapter triangle through Alethe's
    /// checked `la_disequality` rule and a single `or` flattening step.
    fn format_arith_eq_triangle(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let [not_forward, not_reverse, equality] = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "arithmetic equality triangle must have three literals".to_string(),
            });
        };
        let forward = self.format_term(*not_forward);
        let reverse = self.format_term(*not_reverse);
        let equality = self.format_term(*equality);
        let packed = format!("(or {equality} {forward} {reverse})");
        // `la_disequality` fixes the PACKED order (equality first), while this
        // kind's strict validator fixes the FLAT order (equality last), and
        // carcara's `or` is POSITIONAL — measured at this file's `or` arm:
        // premise `(or a b)` with conclusion `(cl b a)` fails with "expected
        // terms to be equal". Unpack in the premise's own order and reach the
        // recorded order with `reordering`, the same adaptation the array
        // extensionality lowering's `FlatReversed` conclusion uses. Emitting
        // the permuted `or` directly would make the whole document `invalid`
        // rather than merely holey.
        Ok(format!(
            "(step {id}.split (cl {packed}) :rule la_disequality)\n\
             (step {id}.flat (cl {equality} {forward} {reverse}) :rule or :premises ({id}.split))\n\
             (step {id} (cl {forward} {reverse} {equality}) :rule reordering :premises ({id}.flat))"
        ))
    }

    /// Lower `a=b => a<=b` (or the reverse bound) through the standard
    /// `la_generic` checker rule.  The native strict checker already fixed the
    /// exact operands and sorts; the signed coefficients below independently
    /// combine `a != b`'s equality branch with the negated bound.
    fn format_arith_eq_implies_bound(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let [not_equality, bound] = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "arithmetic equality implication must have two literals".to_string(),
            });
        };
        Ok(format!(
            "(step {id} (cl {} {}) :rule la_generic :args (-1 1))",
            self.format_term(*not_equality),
            self.format_term(*bound),
        ))
    }

    fn format_unit_farkas_clause(
        &self,
        id: ProofId,
        clause: &[TermId],
        label: &str,
    ) -> Result<String, AlethePrintError> {
        if clause.is_empty() {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: format!("{label} must be non-empty"),
            });
        }
        let coeffs = std::iter::repeat_n("1", clause.len())
            .collect::<Vec<_>>()
            .join(" ");
        Ok(format!(
            "(step {id} {} :rule la_generic :args ({coeffs}))",
            self.format_clause(clause),
        ))
    }

    /// Decode the printed spelling of a CLOSED SMT-LIB bitvector constant into
    /// `(bits_per_digit, case-folded digits)`.
    ///
    /// Only the two literal spellings `#b…` and `#x…` are recognized, and that
    /// restriction is the whole soundness argument of
    /// [`Self::lower_ground_bv_disequality`]: for these two spellings the digit
    /// COUNT determines the sort (`4 * n` / `1 * n` bits) and the digits
    /// determine the value, so two literals of the same radix with the same
    /// digit count but different case-folded digits are necessarily two
    /// DIFFERENT constants of the SAME bitvector sort. The `(_ bvN W)`
    /// spelling is deliberately not accepted — deciding disequality there
    /// needs arbitrary-precision numeric parsing — and keeps its honest `hole`.
    fn printed_bv_literal(s: &str) -> Option<(u32, String)> {
        if let Some(digits) = s.strip_prefix("#b") {
            if digits.is_empty() || !digits.bytes().all(|b| b == b'0' || b == b'1') {
                return None;
            }
            return Some((1, digits.to_string()));
        }
        let digits = s.strip_prefix("#x")?;
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        Some((4, digits.to_ascii_lowercase()))
    }

    /// Lower a premise-free unit `(cl (not (= C1 C2)))` over two DISTINCT
    /// closed bitvector constants to a derivation the external checker
    /// re-derives itself, instead of printing it as a `hole`.
    ///
    /// AY reaches this clause on every "two constants forced equal" conflict:
    /// `eq_transitive` chains the problem's own equalities down to
    /// `(cl (= #b11111010 #b10011101))` and the refutation is closed by
    /// resolving against its negation. The negation is a ground fact, but no
    /// carcara rule CONCLUDES `(cl (not (= t u)))` — `evaluate`
    /// (`checker/rules/extras.rs`) asserts `assert_clause_len(conclusion, 1)`
    /// and then `match_term_err!((= term value) = &conclusion[0])`, i.e. it
    /// only ever proves a POSITIVE unit equality between a term and its
    /// constant-folded value. Emitting `:rule evaluate` on the negated unit is
    /// rejected outright ("term '(not (= …))' is of the wrong form, expected
    /// '(= term value)'"), so a bare rename would have turned `holey` into
    /// `invalid`. The inference is instead spelled out in four steps that are
    /// each an instance of a rule this build implements:
    ///
    /// ```text
    /// (step t.ev (cl (= (= C1 C2) false))    :rule evaluate)
    /// (step t.q  (cl (not (= C1 C2)) false)  :rule equiv1 :premises (t.ev))
    /// (step t.f  (cl (not false))            :rule false)
    /// (step t    (cl (not (= C1 C2)))        :rule resolution :premises (t.q t.f))
    /// ```
    ///
    /// * `evaluate` folds `(= C1 C2)` with `eval_op(Operator::Equals, ..)`,
    ///   which is `Value::Bool(args[0] == args[1])` over `Value::BitVec(value,
    ///   width)`. The gate below guarantees the two operands are same-sort,
    ///   different-value bitvector constants, so the fold is exactly `false`.
    /// * `equiv1` takes the premise `(= φ₁ φ₂)` to the 2-literal clause
    ///   `(cl (not φ₁) φ₂)` — literally this shape.
    /// * `false` proves exactly `(cl (not false))` and nothing else.
    /// * the closing `resolution` reproduces the ORIGINAL printed clause under
    ///   the ORIGINAL step id, so every downstream `:premises` reference and
    ///   AY's own proof IR are untouched.
    ///
    /// The gate reads the PRINTED clause, never the term IR, for the same
    /// reason [`Self::wire_rule_for_printed_step`] does: a problem-scope
    /// surface override can re-spell an internally-constant literal, and the
    /// checker only ever sees the printed text. Everything else — a variable
    /// operand, a `(_ bvN W)` spelling, two constants that are EQUAL (which is
    /// not a theorem at all), an Int/Real/String disequality (where distinct
    /// printed spellings such as `1.0` / `1.00` may denote the same value), a
    /// non-unit clause — returns `None` and keeps the honest `hole`.
    fn lower_ground_bv_disequality(id: ProofId, clause_str: &str) -> Option<String> {
        let inner = clause_str.strip_prefix("(cl ")?.strip_suffix(')')?;
        let literals = split_sexpr_tokens(inner)?;
        let [literal] = literals.as_slice() else {
            return None;
        };
        let negated = split_application(literal, "not")?;
        let [equality] = negated.as_slice() else {
            return None;
        };
        let operands = split_application(equality, "=")?;
        let [lhs, rhs] = operands.as_slice() else {
            return None;
        };
        let (lhs_radix, lhs_digits) = Self::printed_bv_literal(lhs)?;
        let (rhs_radix, rhs_digits) = Self::printed_bv_literal(rhs)?;
        // Same radix AND same digit count => same bitvector sort (carcara
        // would reject an ill-sorted `=` anyway). Different case-folded digits
        // => different values, so `(= C1 C2)` folds to `false`.
        if lhs_radix != rhs_radix || lhs_digits.len() != rhs_digits.len() {
            return None;
        }
        if lhs_digits == rhs_digits {
            return None;
        }
        Some(format!(
            "(step {id}.ev (cl (= {equality} false)) :rule evaluate)\n\
             (step {id}.q (cl {literal} false) :rule equiv1 :premises ({id}.ev))\n\
             (step {id}.f (cl (not false)) :rule false)\n\
             (step {id} {clause_str} :rule resolution :premises ({id}.q {id}.f))"
        ))
    }

    /// Demote a wire rule the pinned checker rejects on the premise/argument
    /// COUNT, for a step printed with neither.
    ///
    /// [`ay_core::is_checkable_alethe_rule`] only asks whether the checker
    /// knows the NAME. That is the right question for a step that supplies
    /// what the rule needs; it is the wrong question for the bare
    /// `(step id (cl …) :rule R)` a theory lemma prints, because a rule like
    /// `string_decompose` (1 premise, 1 arg), `re_inter` (2 premises) or
    /// `concat_unify` (2 premises, 1 arg) is refused on the count before the
    /// checker looks at the clause at all. Measured on carcara 1.1.0
    /// `[git master 9a352ee]`, the bare form answers
    /// `checking failed on step 't0' with rule 'string_decompose': expected 1
    /// premises, got 0` and the document is `invalid`; the same step under
    /// `hole` is `holey`.
    ///
    /// `TheoryLemmaKind::StringContentAxiom` is the kind this actually
    /// affects: it maps to `string_decompose`, a real carcara rule name, so
    /// `wire_rule_name` passed it straight through and AY published a step no
    /// checker run could ever accept. `hole` is the honest rendering — and it
    /// costs nothing in AY's own soundness gates, which read the proof IR and
    /// re-validate the kind through `checker::string_axiom` regardless of what
    /// is printed.
    ///
    /// This never rescues a false certificate: it only ever replaces a name
    /// that is guaranteed to be rejected. A rule the checker could accept bare
    /// is not in the set and passes through unchanged.
    fn wire_rule_for_bare_step(wire: &str) -> &str {
        if ay_core::alethe_rule_requires_premises_or_args(wire) {
            ay_core::UNPROVED_STEP_RULE
        } else {
            wire
        }
    }

    /// Render one exact `bvand(a,b) = bvand(b,a)` unit as Alethe `aci_simp`.
    fn format_binary_bvand_aci_simp(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
            return None;
        };
        if eq != "=" || equality_args.len() != 2 {
            return None;
        }
        let (left, right) = (equality_args[0], equality_args[1]);
        let (
            TermData::App(Symbol::Named(left_op), left_args),
            TermData::App(Symbol::Named(right_op), right_args),
        ) = (self.terms.get(left), self.terms.get(right))
        else {
            return None;
        };
        if left_op != "bvand"
            || right_op != "bvand"
            || left_args.len() != 2
            || right_args.as_slice() != [left_args[1], left_args[0]]
            || self.terms.sort(left) != self.terms.sort(right)
            || !matches!(self.terms.sort(left), Sort::BitVec(_))
        {
            return None;
        }

        // Surface overrides can re-spell an internally checked term. Gate the
        // lowering on the bytes the external checker will actually parse.
        let printed_left = self.format_term(left);
        let printed_right = self.format_term(right);
        let [left_a, left_b] =
            <[String; 2]>::try_from(split_application(&printed_left, "bvand")?).ok()?;
        let [right_a, right_b] =
            <[String; 2]>::try_from(split_application(&printed_right, "bvand")?).ok()?;
        if left_a != right_b || left_b != right_a {
            return None;
        }
        aci_simp_step::ac_identity_step(id, &printed_left, &printed_right)
    }

    /// Lower "these two bit-vector CONSTANTS differ" to Carcara's `evaluate`.
    ///
    /// SUBSET ARGUMENT. `endpoint_refutation_for` (`executor/proof/
    /// authored_linear.rs`) is the producer that reaches this shape: it emits
    /// [`ay_core::TheoryLemmaKind::BvBitBlast`] on the UNIT clause
    /// `(cl (not (= c d)))` only after `is_bitvec_constant` accepted BOTH
    /// endpoints and `recognize_bv_bitblast` re-derived the disequality. This
    /// printer trusts none of that: it re-decodes the clause here and declines
    /// unless it is a one-literal negated `=` over two `Constant::BitVec`
    /// terms of one width with different values.
    ///
    /// Carcara's `evaluate` (`checker/rules/rare.rs`) accepts `(cl (= t v))`
    /// exactly when its own ground evaluator reduces `t` to `v`. On
    /// `(= (= c d) false)` that evaluator does nothing but compare two
    /// bit-vector literals — no bit-vector OPERATOR semantics are involved, so
    /// there is no room for AY's and Carcara's evaluators to disagree. The
    /// clause set this lowering can emit is therefore a strict subset of the
    /// clauses `evaluate` re-derives. `equiv_pos2`/`false`/`resolution` carry
    /// `(= c d) <-> false` to the printed unit `(not (= c d))` and are
    /// premise-checked by Carcara like any other step.
    ///
    /// NEGATIVE DIRECTION. A clause AY may legitimately carry under this kind
    /// but that is NOT an instance — `(cl (not (= (bvadd x #x01) #x05)))`,
    /// `(cl (= (bvand x x) x))`, a two-literal clause, or a pair of EQUAL
    /// constants — fails one of the decodes and keeps the honest `hole`.
    fn format_bv_constant_disequality(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let [literal] = clause else {
            return None;
        };
        let TermData::Not(equality) = self.terms.get(*literal) else {
            return None;
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
            return None;
        };
        if eq != "=" || equality_args.len() != 2 {
            return None;
        }
        let (left, right) = (equality_args[0], equality_args[1]);
        let (
            TermData::Const(Constant::BitVec {
                value: left_value,
                width: left_width,
            }),
            TermData::Const(Constant::BitVec {
                value: right_value,
                width: right_width,
            }),
        ) = (self.terms.get(left), self.terms.get(right))
        else {
            return None;
        };
        if left_width != right_width || left_value == right_value {
            return None;
        }

        // Gate on the BYTES the external checker parses, not on the term IR: a
        // problem-scope surface override can re-spell either side, and only a
        // printed pair that is still two DIFFERENT bit-vector literals of one
        // width is an `evaluate` instance.
        let printed_left = self.format_term(left);
        let printed_right = self.format_term(right);
        let (surface_left, surface_left_width) = parse_printed_bitvec_literal(&printed_left)?;
        let (surface_right, surface_right_width) = parse_printed_bitvec_literal(&printed_right)?;
        if surface_left_width != surface_right_width || surface_left == surface_right {
            return None;
        }
        let equality_text = format!("(= {printed_left} {printed_right})");
        let printed_literal = self.format_term(*literal);
        if printed_literal != format!("(not {equality_text})") {
            return None;
        }

        Some(format!(
            "(step {id}.ev (cl (= {equality_text} false)) :rule evaluate)\n\
             (step {id}.eq (cl (not (= {equality_text} false)) (not {equality_text}) false) :rule equiv_pos2)\n\
             (step {id}.f (cl (not false)) :rule false)\n\
             (step {id}.r (cl (not {equality_text}) false) :rule resolution :premises ({id}.ev {id}.eq))\n\
             (step {id} (cl {printed_literal}) :rule resolution :premises ({id}.r {id}.f))"
        ))
    }

    /// Widest bit-vector this printer will expand into per-bit Alethe steps.
    ///
    /// The expansion is linear in the width (one `@bit_of` pair and one
    /// `*_simplify` step per bit, plus one `cong` premise each), so it needs a
    /// cap. 64 matches `checker::bv_bitblast`'s `MAX_EVALUATED_BV_WIDTH`
    /// (`u64::BITS`) and the widths its bit-blast/LRAT lane is regression-
    /// covered for, so the cap bounds the emitted document without truncating
    /// the range AY routinely certifies. A wider lemma keeps the honest `hole`.
    const MAX_BITBLAST_LOWERING_WIDTH: u32 = 64;

    /// `(bvand t t)` / `(bvor t t)` -> the Alethe surface operator name, the
    /// Carcara bit-blasting rule for it, the Boolean connective that rule
    /// builds each bit from, the simplification rule that discharges that
    /// connective's idempotency, and the repeated operand.
    ///
    /// Every name is spelled out rather than derived from the operator: the
    /// bit-blast rule suffix and the bit connective coincide for `bvand`/`bvor`
    /// but not in general (`bitblast_xnor` builds `=` bits), so deriving one
    /// from the other would be a trap for the next operator added here.
    fn decode_idempotent_bv_gate(
        terms: &TermStore,
        term: TermId,
    ) -> Option<IdempotentBvGate<'static>> {
        let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
            return None;
        };
        let [first, second] = args.as_slice() else {
            return None;
        };
        if first != second {
            return None;
        }
        match op.as_str() {
            "bvand" => Some(("bvand", "bitblast_and", "and", "and_simplify", *first)),
            "bvor" => Some(("bvor", "bitblast_or", "or", "or_simplify", *first)),
            _ => None,
        }
    }

    /// Lower the bit-wise idempotency identity `(bvand t t) = t` /
    /// `(bvor t t) = t` to Carcara's PER-OPERATOR bit-blasting rules.
    ///
    /// AY has one coarse `bv_bitblast` kind where Carcara has a fine-grained
    /// `bitblast_*` suite, and the two are not interchangeable in general:
    /// every `bitblast_*` rule concludes `(= <word-level term> (@bbterm b0 ..
    /// bn))`, i.e. it relates a bit-vector term to an EXPLICIT list of Boolean
    /// bit terms, while an AY `BvBitBlast` clause is a word-level tautology
    /// with no `@bbterm` in it. So the coarse kind cannot be renamed onto a
    /// per-operator rule; it has to be DERIVED as a sequence of them.
    ///
    /// SUBSET ARGUMENT, rule by rule, for the shape this function accepts:
    ///
    /// * `bitblast_and` / `bitblast_or` (`checker/rules/bitvectors.rs`) match
    ///   `(= (bvand ...) res)` / `(= (bvor ...) res)` and require `res` to be
    ///   `(@bbterm ...)` whose i-th argument is `(and x_i y_i)` / `(or x_i
    ///   y_i)` for `x_i`, `y_i` the i-th bits of the two operands. Because
    ///   this function only fires when BOTH operands are the SAME term `t`,
    ///   `x_i` and `y_i` are both `((_ @bit_of i) t)` — exactly what is
    ///   printed.
    /// * `bitblast_var` requires only that the left side is bit-vector-sorted
    ///   and the right side is the `@bbterm` of its `@bit_of` projections; `t`
    ///   is bit-vector-sorted by construction. It does NOT require `t` to be a
    ///   variable, so an opaque compound operand is still in the subset.
    /// * `and_simplify` / `or_simplify` reduce a repeated conjunct/disjunct,
    ///   so `(and b b) = b` and `(or b b) = b` are in their domain.
    /// * `cong`, `trans` and `symm` are premise-checked congruence closure.
    ///
    /// Every step is therefore one Carcara re-derives from the printed text
    /// alone. Nothing here asserts the identity — Carcara proves it.
    ///
    /// NEGATIVE DIRECTION. `(= (bvand x y) x)` (distinct operands),
    /// `(= (bvor x x) y)` (right side is not the operand), `(= (bvxor x x)
    /// #x00)` (a different operator, whose bit-blasting needs `(xor b b) =
    /// false` and NO Carcara rule proves that in one step), a non-unit clause,
    /// and any surface override that breaks the printed operand identity all
    /// return `None` and keep the honest `hole`.
    fn format_bv_idempotent_gate_bitblast(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
            return None;
        };
        if eq != "=" || equality_args.len() != 2 {
            return None;
        }
        let (left, right) = (equality_args[0], equality_args[1]);
        // Exactly one side is the idempotent application and the other side is
        // its repeated operand. `reversed` records the printed orientation so
        // the final step reproduces the clause byte-for-byte.
        let (decoded, reversed) = match Self::decode_idempotent_bv_gate(self.terms, left) {
            Some(decoded) if decoded.4 == right => (decoded, false),
            _ => match Self::decode_idempotent_bv_gate(self.terms, right) {
                Some(decoded) if decoded.4 == left => (decoded, true),
                _ => return None,
            },
        };
        let (operator, blast_rule, connective, simplify_rule, operand) = decoded;
        let application = if reversed { right } else { left };
        let Sort::BitVec(bits) = self.terms.sort(application) else {
            return None;
        };
        let width = bits.width;
        if width == 0 || width > Self::MAX_BITBLAST_LOWERING_WIDTH {
            return None;
        }

        // Gate on the printed bytes: a surface override may re-spell either
        // side, and the derivation is only sound while the printed operands of
        // the gate are the SAME text as the printed other side of the equality.
        let printed_application = self.format_term(application);
        let printed_operand = self.format_term(operand);
        let printed_equality = self.format_term(*equality);
        let oriented_equality = if reversed {
            format!("(= {printed_operand} {printed_application})")
        } else {
            format!("(= {printed_application} {printed_operand})")
        };
        if printed_equality != oriented_equality {
            return None;
        }
        let [surface_first, surface_second] =
            <[String; 2]>::try_from(split_application(&printed_application, operator)?).ok()?;
        if surface_first != surface_second || surface_first != printed_operand {
            return None;
        }

        let operand_bits: Vec<String> = (0..width)
            .map(|index| format!("((_ @bit_of {index}) {printed_operand})"))
            .collect();
        let gate_bits: Vec<String> = operand_bits
            .iter()
            .map(|bit| format!("({connective} {bit} {bit})"))
            .collect();
        let blasted_gate = format!("(@bbterm {})", gate_bits.join(" "));
        let blasted_operand = format!("(@bbterm {})", operand_bits.join(" "));

        let mut output = format!(
            "(step {id}.bb (cl (= {printed_application} {blasted_gate})) :rule {blast_rule})\n\
             (step {id}.var (cl (= {printed_operand} {blasted_operand})) :rule bitblast_var)"
        );
        for (index, (gate_bit, operand_bit)) in
            gate_bits.iter().zip(operand_bits.iter()).enumerate()
        {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id}.b{index} (cl (= {gate_bit} {operand_bit})) :rule {simplify_rule})"
                ),
            );
        }
        let bit_premises: Vec<String> = (0..width).map(|index| format!("{id}.b{index}")).collect();
        let forward_equality = format!("(= {printed_application} {printed_operand})");
        let _ = std::fmt::Write::write_fmt(
            &mut output,
            format_args!(
                "\n(step {id}.cong (cl (= {blasted_gate} {blasted_operand})) :rule cong :premises ({}))\n\
                 (step {id}.lhs (cl (= {printed_application} {blasted_operand})) :rule trans :premises ({id}.bb {id}.cong))\n\
                 (step {id}.rhs (cl (= {blasted_operand} {printed_operand})) :rule symm :premises ({id}.var))",
                bit_premises.join(" ")
            ),
        );
        if reversed {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id}.fwd (cl {forward_equality}) :rule trans :premises ({id}.lhs {id}.rhs))\n\
                     (step {id} (cl {oriented_equality}) :rule symm :premises ({id}.fwd))"
                ),
            );
        } else {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id} (cl {forward_equality}) :rule trans :premises ({id}.lhs {id}.rhs))"
                ),
            );
        }
        Some(output)
    }

    /// A NON-STRICT unsigned comparison -> the Carcara pseudo-Boolean rule for
    /// it, its exact STRICT dual operator, the pseudo-Boolean rule for that
    /// dual, and whether the non-strict side's pseudo-Boolean difference is
    /// taken in the SWAPPED operand order.
    ///
    /// Read off Carcara's `checker/rules/pb_blasting.rs` conclusions directly:
    ///
    /// ```text
    /// pbblast_bvuge : (= (bvuge x y) (>= (- Sx Sy) 0))
    /// pbblast_bvult : (= (bvult x y) (>= (- Sy Sx) 1))
    /// pbblast_bvule : (= (bvule x y) (>= (- Sy Sx) 0))
    /// pbblast_bvugt : (= (bvugt x y) (>= (- Sx Sy) 1))
    /// ```
    ///
    /// So for `bvuge` the non-strict difference is `Sx - Sy` (`swapped =
    /// false`) and its dual's is the reverse; for `bvule` it is `Sy - Sx`
    /// (`swapped = true`) and its dual's is the reverse. In BOTH rows the pair
    /// is `A = (>= D 0)` against `B = (>= -D 1)` for one difference `D`, which
    /// is what makes one derivation cover both.
    ///
    /// This table is exactly `ay_dpll`'s `unsigned_strict_dual` and must stay in
    /// lock-step with it. SIGNED comparisons are excluded from both for the same
    /// reason: `pbblast_bvsge`/`pbblast_bvslt` carry an extra negative-weight
    /// sign summand, so they are a different derivation needing their own
    /// machine-checked witness.
    fn decode_unsigned_compare_duality(
        op: &str,
    ) -> Option<(&'static str, &'static str, &'static str, bool)> {
        match op {
            "bvuge" => Some(("pbblast_bvuge", "bvult", "pbblast_bvult", false)),
            "bvule" => Some(("pbblast_bvule", "bvugt", "pbblast_bvugt", true)),
            _ => None,
        }
    }

    /// The pseudo-Boolean value sum Carcara's `check_pbblast_sum` expects for a
    /// width-`width` bit-vector printed as `bitvector`:
    /// `(+ ((_ @int_of 0) v) (* 2 ((_ @int_of 1) v)) ... (* 2^(w-1) ((_ @int_of w-1) v)))`.
    ///
    /// The i-th summand must carry coefficient exactly `2^i` and index exactly
    /// `i`, and the i==0 coefficient may be — and here is — omitted. At width 1
    /// the sum is the bare summand: `split_summation` takes a non-`+` term as a
    /// one-element sum, and a one-argument `(+ x)` is not well-formed SMT-LIB.
    fn pbblast_value_sum(bitvector: &str, width: u32) -> String {
        let summands: Vec<String> = (0..width)
            .map(|index| {
                let projection = format!("((_ @int_of {index}) {bitvector})");
                if index == 0 {
                    projection
                } else {
                    format!(
                        "(* {} {projection})",
                        num_bigint::BigInt::from(1u8) << index
                    )
                }
            })
            .collect();
        if let [only] = summands.as_slice() {
            return only.clone();
        }
        format!("(+ {})", summands.join(" "))
    }

    /// Lower the unsigned comparison DUALITY `(bvuge a b) = (not (bvult a b))`
    /// (and its `bvule`/`bvugt` mirror) to Carcara's pseudo-Boolean blasting
    /// plus checked linear arithmetic.
    ///
    /// This is the guard-carrier shape a verified code generator's BOUNDS and
    /// SHIFT-RANGE obligations produce: the INTENDED trap set is spelled with
    /// the `bvuge` primitive while the EMITTED x86 `AE` condition code is the
    /// negation of the carry flag, i.e. `(not (bvult a b))`.
    ///
    /// WHY NOT THE `bitblast_*` SUITE, which every other lowering here uses.
    /// Carcara's bit-blasting family has `bitblast_ult` but NO rule whose
    /// conclusion carries `bvuge`, and the bit-level residue of the identity is
    /// not one any `*_simplify` rule discharges. The pseudo-Boolean family does
    /// have both directions, so the identity is reconstructible there instead.
    ///
    /// SUBSET ARGUMENT, rule by rule, for the shape this function accepts. Write
    /// `Sx`/`Sy` for the two `pbblast_value_sum`s, `D` for the non-strict side's
    /// difference, `A = (>= D 0)` and `B = (>= (- D) 1)`.
    ///
    /// * `pbblast_bvuge` / `pbblast_bvule` / `pbblast_bvult` / `pbblast_bvugt`
    ///   (`checker/rules/pb_blasting.rs`) each match exactly the conclusion
    ///   quoted in [`Self::decode_unsigned_compare_duality`] and then re-check
    ///   every summand's coefficient (`2^i`), index (`i`) and bit-vector
    ///   against the operand's own sort. Both sums are printed at the operand's
    ///   FULL width from that same sort, so they are in the strictest sub-case
    ///   of what the rule admits.
    /// * `la_generic` is a Farkas check with real arithmetic over the printed
    ///   linear forms. The two clauses are the two halves of `A <-> ~B`, and
    ///   both need integer strengthening, which Carcara applies because
    ///   `@int_of` is Int-sorted: `(cl (not A) (not B))` negates to `D >= 0` and
    ///   `-D >= 1`, summing to `0 >= 1`; `(cl A B)` negates to `D < 0` and
    ///   `-D < 1`, strengthened to `D <= -1` and `-D <= 0`, summing to
    ///   `0 <= -1`. Both are contradictory, so both clauses are valid — and a
    ///   wrong threshold or a wrong operand order makes the sum NON-contradictory
    ///   and Carcara rejects the step.
    /// * `equiv_neg1` / `equiv_neg2` / `not_not` / `resolution` are the
    ///   propositional bridge from those two clauses to the single equivalence
    ///   `(= A (not B))`; every one is premise-checked.
    /// * `cong`, `trans`, `symm` are premise-checked congruence closure.
    ///
    /// Every step is therefore one Carcara re-derives from the printed text
    /// alone. Nothing here asserts the identity — and nothing here AUTHORIZES
    /// it either: the clause reached this printer only because
    /// `checker::bv_bitblast`'s independent bit-blast/LRAT recognizer already
    /// decided it, so a false pair is refused there before it is ever typeset.
    ///
    /// NEGATIVE DIRECTION. `(= (bvugt a b) (not (bvult a b)))` (a FALSE pair:
    /// the two differ exactly when `a == b`), a mismatched operand order
    /// (`(= (bvuge a b) (not (bvult b a)))`), a signed comparison, a non-unit
    /// clause, an over-cap or zero width, and any surface override that breaks
    /// the printed operand identity all return `None` and keep the honest
    /// `hole`.
    fn format_bv_unsigned_compare_duality(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
            return None;
        };
        if eq != "=" || equality_args.len() != 2 {
            return None;
        }
        let (left, right) = (equality_args[0], equality_args[1]);
        // Exactly one side is the non-strict comparison and the other is the
        // negation of its strict dual. `reversed` records the printed
        // orientation so the final step reproduces the clause byte-for-byte.
        let (non_strict, negated_strict, reversed) =
            match Self::decode_unsigned_compare_operands(self.terms, left, right) {
                Some(()) => (left, right, false),
                None => match Self::decode_unsigned_compare_operands(self.terms, right, left) {
                    Some(()) => (right, left, true),
                    None => return None,
                },
            };
        let TermData::App(Symbol::Named(operator), comparison_args) = self.terms.get(non_strict)
        else {
            return None;
        };
        let (non_strict_rule, strict_operator, strict_rule, swapped) =
            Self::decode_unsigned_compare_duality(operator.as_str())?;
        let [first_operand, _] = comparison_args.as_slice() else {
            return None;
        };
        let Sort::BitVec(bits) = self.terms.sort(*first_operand) else {
            return None;
        };
        let width = bits.width;
        if width == 0 || width > Self::MAX_BITBLAST_LOWERING_WIDTH {
            return None;
        }

        // Gate on the printed bytes: a surface override may re-spell either
        // side, and the derivation is only sound while the two comparisons name
        // the SAME two operands in the SAME order in the PRINTED text.
        let printed_non_strict = self.format_term(non_strict);
        let printed_negated = self.format_term(negated_strict);
        let printed_equality = self.format_term(*equality);
        let oriented_equality = if reversed {
            format!("(= {printed_negated} {printed_non_strict})")
        } else {
            format!("(= {printed_non_strict} {printed_negated})")
        };
        if printed_equality != oriented_equality {
            return None;
        }
        let [printed_strict] =
            <[String; 1]>::try_from(split_application(&printed_negated, "not")?).ok()?;
        let [x, y] =
            <[String; 2]>::try_from(split_application(&printed_non_strict, operator.as_str())?)
                .ok()?;
        let strict_operands =
            <[String; 2]>::try_from(split_application(&printed_strict, strict_operator)?).ok()?;
        if strict_operands != [x.clone(), y.clone()] {
            return None;
        }

        let x_sum = Self::pbblast_value_sum(&x, width);
        let y_sum = Self::pbblast_value_sum(&y, width);
        // `A` is the non-strict side's pseudo-Boolean constraint and `B` its
        // dual's; by the table they always take the difference in OPPOSITE
        // orders, which is exactly what makes `A <-> (not B)` hold.
        let (a_left, a_right) = if swapped {
            (&y_sum, &x_sum)
        } else {
            (&x_sum, &y_sum)
        };
        let constraint_a = format!("(>= (- {a_left} {a_right}) 0)");
        let constraint_b = format!("(>= (- {a_right} {a_left}) 1)");
        let equivalence = format!("(= {constraint_a} (not {constraint_b}))");
        let forward_equality = format!("(= {printed_non_strict} {printed_negated})");

        let mut output = format!(
            "(step {id}.pa (cl (= {printed_non_strict} {constraint_a})) :rule {non_strict_rule})\n\
             (step {id}.pb (cl (= {printed_strict} {constraint_b})) :rule {strict_rule})\n\
             (step {id}.f1 (cl (not {constraint_a}) (not {constraint_b})) :rule la_generic :args (1 1))\n\
             (step {id}.f2 (cl {constraint_a} {constraint_b}) :rule la_generic :args (1 1))\n\
             (step {id}.n1 (cl {equivalence} (not {constraint_a}) (not (not {constraint_b}))) :rule equiv_neg1)\n\
             (step {id}.n2 (cl {equivalence} {constraint_a} (not {constraint_b})) :rule equiv_neg2)\n\
             (step {id}.r1 (cl {equivalence} (not {constraint_b})) :rule resolution :premises ({id}.n2 {id}.f1))\n\
             (step {id}.r2 (cl {equivalence} (not (not {constraint_b})) {constraint_b}) :rule resolution :premises ({id}.n1 {id}.f2))\n\
             (step {id}.r3 (cl {equivalence} (not (not {constraint_b}))) :rule resolution :premises ({id}.r2 {id}.r1))\n\
             (step {id}.nn (cl (not (not (not {constraint_b}))) {constraint_b}) :rule not_not)\n\
             (step {id}.r4 (cl {equivalence} {constraint_b}) :rule resolution :premises ({id}.r3 {id}.nn))\n\
             (step {id}.eq (cl {equivalence}) :rule resolution :premises ({id}.r4 {id}.r1))\n\
             (step {id}.cb (cl (= {printed_negated} (not {constraint_b}))) :rule cong :premises ({id}.pb))\n\
             (step {id}.cbs (cl (= (not {constraint_b}) {printed_negated})) :rule symm :premises ({id}.cb))\n\
             (step {id}.lhs (cl (= {printed_non_strict} (not {constraint_b}))) :rule trans :premises ({id}.pa {id}.eq))"
        );
        if reversed {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id}.fwd (cl {forward_equality}) :rule trans :premises ({id}.lhs {id}.cbs))\n\
                     (step {id} (cl {oriented_equality}) :rule symm :premises ({id}.fwd))"
                ),
            );
        } else {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id} (cl {forward_equality}) :rule trans :premises ({id}.lhs {id}.cbs))"
                ),
            );
        }
        Some(output)
    }

    /// Does `non_strict` hold an unsigned non-strict comparison whose exact
    /// negated strict dual, over the SAME operands in the SAME order, is
    /// `negated_strict`? Mirrors `ay_dpll`'s `is_unsigned_compare_duality_of`.
    fn decode_unsigned_compare_operands(
        terms: &TermStore,
        non_strict: TermId,
        negated_strict: TermId,
    ) -> Option<()> {
        let TermData::App(Symbol::Named(operator), comparison_args) = terms.get(non_strict) else {
            return None;
        };
        let (_, strict_operator, _, _) = Self::decode_unsigned_compare_duality(operator.as_str())?;
        let [x, y] = comparison_args.as_slice() else {
            return None;
        };
        let (x, y) = (*x, *y);
        let inner = match terms.get(negated_strict) {
            TermData::Not(inner) => *inner,
            TermData::App(Symbol::Named(name), args) if name == "not" && args.len() == 1 => args[0],
            _ => return None,
        };
        let TermData::App(Symbol::Named(inner_operator), inner_args) = terms.get(inner) else {
            return None;
        };
        (inner_operator.as_str() == strict_operator
            && inner_args.as_slice() == [x, y]
            && matches!(terms.sort(x), Sort::BitVec(_))
            && terms.sort(x) == terms.sort(y))
        .then_some(())
    }

    /// `(bvnot t)` -> `t`.
    fn decode_bvnot(terms: &TermStore, term: TermId) -> Option<TermId> {
        let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
            return None;
        };
        let [only] = args.as_slice() else {
            return None;
        };
        (op == "bvnot").then_some(*only)
    }

    /// Lower the double-negation identity `(bvnot (bvnot t)) = t` to Carcara's
    /// per-operator bit-blasting.
    ///
    /// This is the NESTED case of the same technique as
    /// [`Self::format_bv_idempotent_gate_bitblast`]: a `bitblast_*` rule can
    /// only relate ONE word-level operator to a `@bbterm`, so an operator
    /// applied to an operator is blasted bottom-up and bridged with `cong`.
    ///
    /// SUBSET ARGUMENT. Carcara's `bitblast_not` (`checker/rules/
    /// bitvectors.rs`) matches `(= (bvnot x) res)` and requires `res` to be the
    /// `@bbterm` whose i-th argument is `(not x_i)`, where `x_i` is the i-th
    /// bit of `x` — its own `@bbterm` argument when `x` is one, and
    /// `((_ @bit_of i) x)` otherwise. Both uses here are exactly that:
    ///
    /// * on the inner `(bvnot t)`, `t` is not a `@bbterm`, so the bits are the
    ///   printed `((_ @bit_of i) t)`;
    /// * on the rewritten outer `(bvnot (@bbterm (not t_i) ...))`, the argument
    ///   IS a `@bbterm`, so Carcara reuses its arguments and the expected
    ///   result is `(@bbterm (not (not t_i)) ...)` — again exactly what is
    ///   printed.
    ///
    /// `not_simplify` reduces a double negation, so `(= (not (not p)) p)` is in
    /// its domain; `bitblast_var`, `cong`, `trans` and `symm` are as in the
    /// idempotency lowering. Carcara re-derives every step from the printed
    /// text.
    ///
    /// NEGATIVE DIRECTION. A single `(bvnot t) = t'` (not a double negation),
    /// `(bvnot (bvnot t)) = u` for `u` other than `t`, a mixed nest such as
    /// `(bvnot (bvneg t)) = t`, a non-unit clause, an over-cap width, and any
    /// surface override that breaks the printed nesting all return `None` and
    /// keep the honest `hole`.
    fn format_bv_double_negation_bitblast(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let [equality] = clause else {
            return None;
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*equality) else {
            return None;
        };
        if eq != "=" || equality_args.len() != 2 {
            return None;
        }
        let (left, right) = (equality_args[0], equality_args[1]);
        let double = |term: TermId| {
            Self::decode_bvnot(self.terms, term)
                .and_then(|inner| Self::decode_bvnot(self.terms, inner))
        };
        let reversed = match double(left) {
            Some(operand) if operand == right => false,
            _ => match double(right) {
                Some(operand) if operand == left => true,
                _ => return None,
            },
        };
        let (outer, operand) = if reversed {
            (right, left)
        } else {
            (left, right)
        };
        let inner = Self::decode_bvnot(self.terms, outer)?;
        let Sort::BitVec(bits) = self.terms.sort(outer) else {
            return None;
        };
        let width = bits.width;
        if width == 0 || width > Self::MAX_BITBLAST_LOWERING_WIDTH {
            return None;
        }

        // Gate on the printed bytes, exactly as the idempotency lane does.
        let printed_outer = self.format_term(outer);
        let printed_inner = self.format_term(inner);
        let printed_operand = self.format_term(operand);
        let printed_equality = self.format_term(*equality);
        let oriented_equality = if reversed {
            format!("(= {printed_operand} {printed_outer})")
        } else {
            format!("(= {printed_outer} {printed_operand})")
        };
        if printed_equality != oriented_equality {
            return None;
        }
        let [outer_argument] =
            <[String; 1]>::try_from(split_application(&printed_outer, "bvnot")?).ok()?;
        let [inner_argument] =
            <[String; 1]>::try_from(split_application(&printed_inner, "bvnot")?).ok()?;
        if outer_argument != printed_inner || inner_argument != printed_operand {
            return None;
        }

        let operand_bits: Vec<String> = (0..width)
            .map(|index| format!("((_ @bit_of {index}) {printed_operand})"))
            .collect();
        let once: Vec<String> = operand_bits
            .iter()
            .map(|bit| format!("(not {bit})"))
            .collect();
        let twice: Vec<String> = once.iter().map(|bit| format!("(not {bit})")).collect();
        let blasted_inner = format!("(@bbterm {})", once.join(" "));
        let blasted_outer = format!("(@bbterm {})", twice.join(" "));
        let blasted_operand = format!("(@bbterm {})", operand_bits.join(" "));

        let mut output = format!(
            "(step {id}.in (cl (= {printed_inner} {blasted_inner})) :rule bitblast_not)\n\
             (step {id}.lift (cl (= {printed_outer} (bvnot {blasted_inner}))) :rule cong :premises ({id}.in))\n\
             (step {id}.out (cl (= (bvnot {blasted_inner}) {blasted_outer})) :rule bitblast_not)"
        );
        for (index, (double_bit, operand_bit)) in twice.iter().zip(operand_bits.iter()).enumerate()
        {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id}.b{index} (cl (= {double_bit} {operand_bit})) :rule not_simplify)"
                ),
            );
        }
        let bit_premises: Vec<String> = (0..width).map(|index| format!("{id}.b{index}")).collect();
        let forward_equality = format!("(= {printed_outer} {printed_operand})");
        let _ = std::fmt::Write::write_fmt(
            &mut output,
            format_args!(
                "\n(step {id}.cong (cl (= {blasted_outer} {blasted_operand})) :rule cong :premises ({}))\n\
                 (step {id}.var (cl (= {printed_operand} {blasted_operand})) :rule bitblast_var)\n\
                 (step {id}.rhs (cl (= {blasted_operand} {printed_operand})) :rule symm :premises ({id}.var))",
                bit_premises.join(" ")
            ),
        );
        let chain = format!("{id}.lift {id}.out {id}.cong {id}.rhs");
        if reversed {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id}.fwd (cl {forward_equality}) :rule trans :premises ({chain}))\n\
                     (step {id} (cl {oriented_equality}) :rule symm :premises ({id}.fwd))"
                ),
            );
        } else {
            let _ = std::fmt::Write::write_fmt(
                &mut output,
                format_args!(
                    "\n(step {id} (cl {forward_equality}) :rule trans :premises ({chain}))"
                ),
            );
        }
        Some(output)
    }

    /// Alethe's `true` rule proves exactly this clause and nothing else.
    const TRUE_AXIOM_CLAUSE: &'static str = "(cl true)";
    /// Alethe's `false` rule proves exactly this clause and nothing else.
    const FALSE_AXIOM_CLAUSE: &'static str = "(cl (not false))";

    /// Final wire-name decision for one printed step.
    ///
    /// Passing [`ay_core::is_checkable_alethe_rule`] is necessary but not
    /// sufficient: a name can be real *and* misapplied, which the checker
    /// rejects just as hard as an invented one. Two Alethe rules have a FIXED
    /// conclusion — `true` proves exactly `(cl true)`, `false` proves exactly
    /// `(cl (not false))` — while AY's `AletheRule::True`/`False` are Tseitin
    /// bool-constant units admitted by the wider internal bool-tautology
    /// validator (`checker/mod.rs`). Measured divergence: on
    /// `QF_DT/20172804-Barrett/.../v1l20005.cvc.smt2` AY prints
    /// `(step t1 (cl (not (and …))) :rule false)` and carcara answers
    /// `expected term 'false' to be boolean constant '(and …)'` => `invalid`
    /// for the whole document. So:
    ///
    /// * `true`/`false` whose printed conclusion is NOT the axiom is demoted
    ///   to an honest `hole`;
    /// * a `hole` whose printed conclusion IS the axiom (it arrived under a
    ///   coarse kind such as `TheoryLemmaKind::BoolTautology`) is promoted to
    ///   the real, checked rule.
    ///
    /// The gate reads the PRINTED clause, not the term IR, and that is
    /// load-bearing: a problem-scope surface override can print an internally
    /// bool-constant literal in the source problem's own spelling, so an
    /// IR-driven gate promotes steps carcara then rejects (that is exactly how
    /// v1l20005 was found). The checker only ever sees the printed text.
    ///
    /// `allow_promote` is false for steps carrying premises: the two axioms
    /// are premise-free, so promotion is only offered where it is meaningful.
    fn wire_rule_for_printed_step<'r>(
        wire: &'r str,
        clause_str: &str,
        allow_promote: bool,
    ) -> &'r str {
        match wire {
            "true" if clause_str != Self::TRUE_AXIOM_CLAUSE => ay_core::UNPROVED_STEP_RULE,
            "false" if clause_str != Self::FALSE_AXIOM_CLAUSE => ay_core::UNPROVED_STEP_RULE,
            w if allow_promote && w == ay_core::UNPROVED_STEP_RULE => match clause_str {
                Self::TRUE_AXIOM_CLAUSE => "true",
                Self::FALSE_AXIOM_CLAUSE => "false",
                _ => w,
            },
            w => w,
        }
    }

    /// Lower AY's Skolemized array-extensionality certificate to Carcara's
    /// `arrays_ext`.
    ///
    /// AY's clause is the conservative-extension disjunction
    /// `(= a b) ∨ ¬(= (select a K) (select b K))`, where `K` is the fresh diff
    /// witness. Carcara instead derives the UNIT `¬(= (select a K) (select b K))`
    /// from the premise `¬(= a b)`, with `K` fixed to its own epsilon term. So:
    ///
    ///  * [`Self::prepare_array_extensionality_choices`] has already made every
    ///    printed occurrence of the witness — here and in every downstream ROW,
    ///    congruence and resolution step — spell that exact epsilon term;
    ///  * the disjunction is recovered by discharging `¬(= a b)` through a local
    ///    subproof (`subproof` + `not_not` + `resolution`), mirroring the ROW2
    ///    guard handling;
    ///  * `or_neg` + `resolution` repack the two literals into the unit `or`
    ///    term AY's later `or_pos` steps consume, so no premise reference moves.
    ///
    /// Every reconstruction is checked against the ACTUALLY PRINTED clause
    /// before it is emitted: if a surface override, an unrecognized shape, a
    /// multi-level chain, or a missing witness installation makes the rebuilt
    /// text differ by one byte, the lemma is refused and the caller keeps
    /// failing closed instead of publishing a derivation of something else.
    fn format_array_extensionality(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let refuse = || AlethePrintError::UnsupportedArrayExtensionality { id };
        let Some((array_a, array_b, witness)) =
            crate::checker::recognize_array_extensionality(self.terms, clause)
        else {
            return Err(refuse());
        };
        // The witness must be rendered as the epsilon term EVERYWHERE, not just
        // inside this step; that is what `prepare_array_extensionality_choices`
        // installs. Without it the step would claim `arrays_ext` for a free
        // constant Carcara has no reason to believe anything about.
        let Some(installed) = self.skolem_overrides.borrow().get(&witness).cloned() else {
            return Err(refuse());
        };
        let expected_choice = self.array_ext_choice_term(array_a, array_b, witness);
        if installed != expected_choice {
            return Err(refuse());
        }

        let a = self.format_term(array_a);
        let b = self.format_term(array_b);
        let equality = format!("(= {a} {b})");
        let negated_select = format!("(not (= (select {a} {installed}) (select {b} {installed})))");
        let disjunction = format!("(or {equality} {negated_select})");

        // How the clause is ACTUALLY printed decides the tail of the
        // derivation; nothing is inferred from the internal representation.
        enum Conclusion {
            /// `(cl (or (= a b) (not (= (select a K) (select b K)))))`
            PackedOr,
            /// `(cl (= a b) (not (= (select a K) (select b K))))`
            Flat,
            /// `(cl (not (= (select a K) (select b K))) (= a b))`
            FlatReversed,
        }
        let conclusion = match clause {
            [packed] if self.format_term(*packed) == disjunction => Conclusion::PackedOr,
            [first, second] => match (self.format_term(*first), self.format_term(*second)) {
                (f, s) if f == equality && s == negated_select => Conclusion::Flat,
                (f, s) if f == negated_select && s == equality => Conclusion::FlatReversed,
                _ => return Err(refuse()),
            },
            _ => return Err(refuse()),
        };

        // Discharge `¬(= a b)` so the two-literal disjunction reappears. The
        // last step of this prefix is named `{id}` itself in the `Flat` case,
        // so that no extra single-premise step is needed.
        let flat_step = match conclusion {
            Conclusion::Flat => format!("{id}"),
            Conclusion::PackedOr | Conclusion::FlatReversed => format!("{id}.flat"),
        };
        let mut out = String::new();
        out.push_str(&format!(
            "(anchor :step {id}.sp)\n\
             (assume {id}.h (not {equality}))\n\
             (step {id}.ext (cl {negated_select}) :rule arrays_ext :premises ({id}.h))\n\
             (step {id}.sp (cl (not (not {equality})) {negated_select}) \
             :rule subproof :discharge ({id}.h))\n\
             (step {id}.nn (cl (not (not (not {equality}))) {equality}) :rule not_not)\n\
             (step {flat_step} (cl {equality} {negated_select}) \
             :rule resolution :premises ({id}.sp {id}.nn))"
        ));
        match conclusion {
            Conclusion::Flat => {}
            Conclusion::FlatReversed => {
                out.push_str(&format!(
                    "\n(step {id} (cl {negated_select} {equality}) \
                     :rule reordering :premises ({flat_step}))"
                ));
            }
            // Repack into the unit `or` term AY's later `or_pos` steps consume,
            // exactly as the ROW2 lowering does.
            Conclusion::PackedOr => {
                out.push_str(&format!(
                    "\n(step {id}.o0 (cl {disjunction} (not {equality})) :rule or_neg :args (0))\n\
                     (step {id}.r0 (cl {negated_select} {disjunction}) \
                     :rule resolution :premises ({flat_step} {id}.o0))\n\
                     (step {id}.o1 (cl {disjunction} (not {negated_select})) \
                     :rule or_neg :args (1))\n\
                     (step {id} (cl {disjunction}) \
                     :rule resolution :premises ({id}.r0 {id}.o1))"
                ));
            }
        }
        Ok(out)
    }

    /// Lower AY's internally checked ROW1/ROW2 lemmas to the array rules
    /// supported by the pinned Carcara dialect.
    ///
    /// Unit ROW1 is a direct `arrays_idx` theorem. Conditional ROW1 transports
    /// that theorem across an assumed index equality with `cong` and `trans`.
    /// ROW2 assumes the index disequality and uses `arrays_row`. Both guarded
    /// cases are discharged through local subproofs, and ROW2 restores AY's
    /// positive guard (rather than leaving a double negation) with `not_not`
    /// plus resolution. Reversed row equalities get an explicit `symm`/`trans`
    /// derivation; malformed surface overrides fail closed.
    fn format_array_select_store(
        &self,
        id: ProofId,
        clause: &[TermId],
        index_eq: bool,
    ) -> Result<String, AlethePrintError> {
        use crate::checker::ArraySelectStorePrinterTerms as Row;

        let Some(shape) =
            crate::checker::array_select_store_printer_terms(self.terms, clause, index_eq)
        else {
            return Err(AlethePrintError::InvalidArrayStep {
                id,
                reason: format!(
                    "ROW lemma {} is outside the checked top-level arrays_idx/arrays_row subset",
                    self.format_clause(clause)
                ),
            });
        };

        let invalid_surface = |reason: String| AlethePrintError::InvalidArrayStep { id, reason };
        match shape {
            Row::Row1 {
                row,
                select,
                base_array,
                store_index,
                value: value_term,
                read_index,
                guard,
                packed_or,
            } => {
                let base = self.format_term(base_array);
                let store_index = self.format_term(store_index);
                let value = self.format_term(value_term);
                let read_index = self.format_term(read_index);
                let printed_select = self.format_term(select);
                let Some(select_args) = split_application(&printed_select, "select") else {
                    return Err(invalid_surface(
                        "ROW1 select surface is not a select application".to_string(),
                    ));
                };
                let [printed_store, printed_read_index] = select_args.as_slice() else {
                    return Err(invalid_surface(
                        "ROW1 select surface has malformed arity".to_string(),
                    ));
                };
                let Some(store_args) = split_application(printed_store, "store") else {
                    return Err(invalid_surface(
                        "ROW1 select surface does not read a store".to_string(),
                    ));
                };
                let [printed_base, printed_store_index, stored_value] = store_args.as_slice()
                else {
                    return Err(invalid_surface(
                        "ROW1 store surface has malformed arity".to_string(),
                    ));
                };
                // Carcara reads the step as PARSED terms, so the surface is
                // faithful to the certified lemma when each position is the
                // same term to its parser — `same_printed_term`: byte identity
                // first, then the bit-vector literal re-spellings (`#x00000000`
                // for `#b0…0`) a problem file may legitimately use. That is a
                // spelling predicate only: a different value, a different
                // width, or a different application shape still refuses here.
                // The certified chain in the problem's write order is the same
                // array, but no pinned rule spells it (`reordered_row_store`).
                let store_reordered = if !surface_literal::same_printed_term(printed_base, &base)
                    || !surface_literal::same_printed_term(printed_store_index, &store_index)
                    || !surface_literal::same_printed_term(printed_read_index, &read_index)
                {
                    if let Some(bridge) = self.format_array_zero_index_bridge(id, clause) {
                        return Ok(bridge);
                    }
                    if !(surface_literal::same_printed_term(printed_read_index, &read_index)
                        && reordered_row_store::reorders_certified_store(
                            printed_store,
                            &base,
                            &store_index,
                            &value,
                        ))
                    {
                        return Err(invalid_surface(format!(
                            "ROW1 select/store surface override changes the certified array or index: \
                                 base={printed_base:?}/{base:?}, \
                                 store_index={printed_store_index:?}/{store_index:?}, \
                                 read_index={printed_read_index:?}/{read_index:?}"
                        )));
                    }
                    true
                } else {
                    false
                };
                let needs_value_bridge =
                    !store_reordered && !surface_literal::same_printed_term(stored_value, &value);
                if needs_value_bridge {
                    let canonical_is_numeric = matches!(
                        self.terms.get(value_term),
                        TermData::Const(Constant::Int(_) | Constant::Rational(_))
                    );
                    // The bridge below states the identity as `poly_simp`,
                    // so it is admitted by the checker's own `poly_simp`
                    // test over the two printed spellings, not only by AY's
                    // numeric reading of them (`printed_poly_simp_holds`).
                    let surface_values_match = canonical_is_numeric
                        && crate::la_generic_signs::parse_numeric_constant(stored_value)
                            .zip(crate::la_generic_signs::parse_numeric_constant(&value))
                            .is_some_and(|(stored, canonical)| stored == canonical)
                        && la_generic_surface::printed_poly_simp_holds(stored_value, &value)
                            == Some(true);
                    if !surface_values_match {
                        return Err(invalid_surface(
                            "ROW1 store-value surface mismatch is not an equivalent numeric literal"
                                .to_string(),
                        ));
                    }
                }

                let canonical_row = format!("(= {printed_select} {value})");
                let reversed_row = format!("(= {value} {printed_select})");
                let printed_row = self.format_term(row);
                // Orientation is decided once, under carcara's term identity,
                // and every later branch reads THIS answer instead of
                // re-comparing the bytes — otherwise a row printed in the
                // certified orientation with a re-spelled literal would be
                // emitted through the `symm` arm and state the reverse.
                let row_is_canonical =
                    surface_literal::same_printed_term(&printed_row, &canonical_row);
                if !row_is_canonical
                    && !surface_literal::same_printed_term(&printed_row, &reversed_row)
                {
                    return Err(invalid_surface(
                        "ROW1 equality surface override is neither the certified orientation nor its symmetry"
                            .to_string(),
                    ));
                }
                if store_reordered {
                    return Err(self.reordered_row1_refusal(
                        id,
                        [guard, packed_or],
                        [&store_index, &read_index],
                        &printed_row,
                    ));
                }

                let Some(guard) = guard else {
                    if !needs_value_bridge {
                        if row_is_canonical {
                            return Ok(format!(
                                "(step {id} (cl {canonical_row}) :rule arrays_idx)"
                            ));
                        }
                        return Ok(format!(
                            "(step {id}.idx (cl {canonical_row}) :rule arrays_idx)\n\
                             (step {id} (cl {reversed_row}) :rule symm :premises ({id}.idx))"
                        ));
                    }

                    let stored_row = format!("(= {printed_select} {stored_value})");
                    if row_is_canonical {
                        return Ok(format!(
                            "(step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                             (step {id}.val (cl (= {stored_value} {value})) :rule poly_simp)\n\
                             (step {id} (cl {canonical_row}) :rule trans :premises ({id}.idx {id}.val))"
                        ));
                    }
                    return Ok(format!(
                        "(step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                         (step {id}.val (cl (= {stored_value} {value})) :rule poly_simp)\n\
                         (step {id}.base (cl {canonical_row}) :rule trans :premises ({id}.idx {id}.val))\n\
                         (step {id} (cl {reversed_row}) :rule symm :premises ({id}.base))"
                    ));
                };

                let printed_guard = self.format_term(guard);
                let guard_forward = format!("(not (= {store_index} {read_index}))");
                let guard_reverse = format!("(not (= {read_index} {store_index}))");
                // Read the guard's orientation once, under the same term
                // identity, and let every arm below consult that answer.
                let mut index_surface_bridge = String::new();
                let mut index_equality_premise = format!("{id}.h");
                let (assumed_equality, guard_is_forward) = if surface_literal::same_printed_term(
                    &printed_guard,
                    &guard_forward,
                ) {
                    (format!("(= {store_index} {read_index})"), true)
                } else if surface_literal::same_printed_term(&printed_guard, &guard_reverse) {
                    (format!("(= {read_index} {store_index})"), false)
                } else if let Some(bridge) = self.format_row1_guard_index_bridge(
                    id,
                    &printed_guard,
                    &store_index,
                    &read_index,
                ) {
                    // An ancestor-level authored override shadowing a
                    // child-level one (the equality node carries the
                    // authored `(= x 0)` while the read index alone carries
                    // the authored `(+ x 0)`) spells ONE certified pair two
                    // ways. Assume the guard's own text and CARRY it to the
                    // certified pair with checked `poly_simp`/`trans`,
                    // rather than emitting a `cong` premise that names a
                    // term the checker reads differently.
                    index_surface_bridge = bridge.steps;
                    index_equality_premise = bridge.premise;
                    (bridge.assumed_equality, bridge.forward)
                } else {
                    // Name the three spellings, exactly as the select/store
                    // surface refusal above does: the guard, the index pair
                    // it must be, and its symmetry. Without them a guard
                    // that prints as neither is unactionable.
                    return Err(invalid_surface(format!(
                            "conditional ROW1 guard surface override changes the certified index pair: \
                                 guard={printed_guard:?}, expected={guard_forward:?} or {guard_reverse:?}"
                        )));
                };
                let same_index_select = format!("(select {printed_store} {store_index})");
                let flat_id = packed_or.map_or_else(|| id.to_string(), |_| format!("{id}.flat"));
                let stored_row = format!("(= {same_index_select} {stored_value})");
                let (cong_row, cong_to_same) = if guard_is_forward {
                    (
                        format!("(= {same_index_select} {printed_select})"),
                        format!(
                            "(step {id}.congs (cl (= {printed_select} {same_index_select})) :rule symm :premises ({id}.cong))"
                        ),
                    )
                } else {
                    (
                        format!("(= {printed_select} {same_index_select})"),
                        String::new(),
                    )
                };
                let cong_premise = if guard_is_forward {
                    format!("{id}.congs")
                } else {
                    format!("{id}.cong")
                };
                let mut output = format!(
                    "(anchor :step {flat_id})\n\
                     (assume {id}.h {assumed_equality})\n\
                     {index_surface_bridge}\
                     (step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                     (step {id}.cong (cl {cong_row}) :rule cong :premises ({index_equality_premise}))"
                );
                if !cong_to_same.is_empty() {
                    output.push('\n');
                    output.push_str(&cong_to_same);
                }
                if needs_value_bridge {
                    let _ = std::fmt::Write::write_fmt(
                        &mut output,
                        format_args!(
                            "\n(step {id}.val (cl (= {stored_value} {value})) :rule poly_simp)\n\
                             (step {id}.base (cl {canonical_row}) :rule trans :premises ({cong_premise} {id}.idx {id}.val))"
                        ),
                    );
                } else {
                    let _ = std::fmt::Write::write_fmt(
                        &mut output,
                        format_args!(
                            "\n(step {id}.base (cl {canonical_row}) :rule trans :premises ({cong_premise} {id}.idx))"
                        ),
                    );
                }
                if !row_is_canonical {
                    let _ = std::fmt::Write::write_fmt(
                        &mut output,
                        format_args!(
                            "\n(step {id}.row (cl {reversed_row}) :rule symm :premises ({id}.base))"
                        ),
                    );
                }
                let _ = std::fmt::Write::write_fmt(
                    &mut output,
                    format_args!(
                        "\n(step {flat_id} (cl {printed_guard} {printed_row}) :rule subproof :discharge ({id}.h))"
                    ),
                );
                self.finish_array_packed_or(
                    id,
                    packed_or,
                    flat_id.as_str(),
                    printed_guard.as_str(),
                    printed_row.as_str(),
                    output,
                )
            }
            Row::Row2 {
                row,
                select_store,
                select_base,
                base_array,
                store_index,
                value: value_term,
                read_index,
                guard,
                packed_or,
            } => {
                let base = self.format_term(base_array);
                let store_index = self.format_term(store_index);
                let read_index = self.format_term(read_index);
                let printed_select_store = self.format_term(select_store);
                let printed_select_base = self.format_term(select_base);
                let Some(store_select_args) = split_application(&printed_select_store, "select")
                else {
                    return Err(invalid_surface(
                        "ROW2 store-side surface is not a select application".to_string(),
                    ));
                };
                let [printed_store, printed_store_read_index] = store_select_args.as_slice() else {
                    return Err(invalid_surface(
                        "ROW2 store-side select has malformed arity".to_string(),
                    ));
                };
                let Some(store_args) = split_application(printed_store, "store") else {
                    return Err(invalid_surface(
                        "ROW2 store-side select does not read a store".to_string(),
                    ));
                };
                let [printed_base, printed_store_index, _printed_value] = store_args.as_slice()
                else {
                    return Err(invalid_surface(
                        "ROW2 store surface has malformed arity".to_string(),
                    ));
                };
                let Some(base_select_args) = split_application(&printed_select_base, "select")
                else {
                    return Err(invalid_surface(
                        "ROW2 base-side surface is not a select application".to_string(),
                    ));
                };
                let [printed_select_base_array, printed_base_read_index] =
                    base_select_args.as_slice()
                else {
                    return Err(invalid_surface(
                        "ROW2 base-side select has malformed arity".to_string(),
                    ));
                };
                // The certified chain in the problem's write order is the same
                // array, but no pinned rule spells it (`reordered_row_store`).
                let store_reordered = if printed_base != &base
                    || printed_store_index != &store_index
                    || printed_store_read_index != &read_index
                    || printed_select_base_array != &base
                    || printed_base_read_index != &read_index
                {
                    if !(printed_store_read_index == &read_index
                        && printed_select_base_array == &base
                        && printed_base_read_index == &read_index
                        && reordered_row_store::reorders_certified_store(
                            printed_store,
                            &base,
                            &store_index,
                            &self.format_term(value_term),
                        ))
                    {
                        return Err(invalid_surface(format!(
                            "ROW2 select surface override changes the certified array or indices: \
                                 store={printed_store:?}/(store {base} {store_index} ..), \
                                 base_select_array={printed_select_base_array:?}, \
                                 read_index={printed_store_read_index:?}/{printed_base_read_index:?}/{read_index:?}"
                        )));
                    }
                    true
                } else {
                    false
                };
                let canonical_row = format!("(= {printed_select_store} {printed_select_base})");
                let reversed_row = format!("(= {printed_select_base} {printed_select_store})");
                let printed_row = self.format_term(row);
                if printed_row != canonical_row && printed_row != reversed_row {
                    return Err(invalid_surface(
                        "ROW2 equality surface override is neither the certified orientation nor its symmetry"
                            .to_string(),
                    ));
                }

                let printed_guard = self.format_term(guard);
                let guard_forward = format!("(= {store_index} {read_index})");
                let guard_reverse = format!("(= {read_index} {store_index})");
                // `arrays_row` reads the store index and the read index off its
                // premise POSITIONALLY: the premise must literally spell
                // `(not (= store_index read_index))`. When AY's own guard is
                // the symmetric spelling, bridge it with `not_symm` rather than
                // handing Carcara a premise it will reject ("expected terms to
                // be equal: i0 and i1").
                let (assumed_disequality, row_premise, orientation_bridge) = if printed_guard
                    == guard_forward
                {
                    (format!("(not {guard_forward})"), format!("{id}.h"), None)
                } else if printed_guard == guard_reverse {
                    (
                        format!("(not {guard_reverse})"),
                        format!("{id}.hs"),
                        Some(format!(
                            "(step {id}.hs (cl (not {guard_forward})) \
                                 :rule not_symm :premises ({id}.h))\n"
                        )),
                    )
                } else {
                    return Err(invalid_surface(
                        "ROW2 guard surface override changes the certified index pair".to_string(),
                    ));
                };
                if store_reordered {
                    return Err(self.reordered_row2_refusal(
                        id,
                        packed_or,
                        &printed_guard,
                        &printed_row,
                    ));
                }
                let orientation_bridge = orientation_bridge.unwrap_or_default();

                let row_derivation = if printed_row == canonical_row {
                    format!(
                        "{orientation_bridge}\
                         (step {id}.row (cl {canonical_row}) :rule arrays_row \
                         :premises ({row_premise}))"
                    )
                } else {
                    format!(
                        "{orientation_bridge}\
                         (step {id}.base (cl {canonical_row}) :rule arrays_row \
                         :premises ({row_premise}))\n\
                         (step {id}.row (cl {reversed_row}) :rule symm :premises ({id}.base))"
                    )
                };
                let flat_id = packed_or.map_or_else(|| id.to_string(), |_| format!("{id}.flat"));
                let output = format!(
                    "(anchor :step {id}.sp)\n\
                     (assume {id}.h {assumed_disequality})\n\
                     {row_derivation}\n\
                     (step {id}.sp (cl (not {assumed_disequality}) {printed_row}) :rule subproof :discharge ({id}.h))\n\
                     (step {id}.nn (cl (not (not {assumed_disequality})) {printed_guard}) :rule not_not)\n\
                     (step {flat_id} (cl {printed_guard} {printed_row}) :rule resolution :premises ({id}.sp {id}.nn))"
                );
                self.finish_array_packed_or(
                    id,
                    packed_or,
                    flat_id.as_str(),
                    printed_guard.as_str(),
                    printed_row.as_str(),
                    output,
                )
            }
        }
    }

    /// Lower an internally checked `ArrayRowChain` lemma to Carcara's
    /// `arrays_idx` / `arrays_row` / `cong` / `trans` rules.
    ///
    /// The chain walk that AY's checker performed
    /// (`validate_array_row_chain`) is replayed one `store` at a time: each
    /// skipped write becomes an `arrays_row` step discharged against the
    /// clause's own index-equality guard, the terminating write becomes
    /// `arrays_idx`, and `trans` composes them. Sub-schema (B) additionally
    /// transports the two walks across the assumed array equality with `cong`.
    /// Everything happens inside ONE subproof whose assumptions are exactly
    /// the negations of the clause literals, so the closing `resolution`
    /// reproduces the original clause byte-for-byte.
    ///
    /// Returns `None` — leaving the caller to emit the faithful, externally
    /// uncheckable `read_over_write_chain` rule name — whenever the printed
    /// surface is not the compositional rendering of the certified terms (a
    /// `let`-abbreviated array equality, a re-spelled `store`, a guard printed
    /// as neither orientation of its index pair). Reconstructing a derivation
    /// from strings that do not correspond to the certified terms is exactly
    /// the failure mode this fails closed on.
    fn format_array_row_chain(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        use crate::checker::ArrayRowChainPrinterTerms as Shape;

        let shape = crate::checker::array_row_chain_printer_terms(self.terms, clause)?;
        let (flat_lits, packed): (Vec<TermId>, Option<TermId>) = match clause {
            [single] => match self.terms.get(*single) {
                TermData::App(Symbol::Named(symbol), args) if symbol == "or" && args.len() >= 2 => {
                    (args.clone(), Some(*single))
                }
                _ => (clause.to_vec(), None),
            },
            _ => (clause.to_vec(), None),
        };
        let flat_id = if packed.is_some() {
            format!("{id}.flat")
        } else {
            id.to_string()
        };

        let mut lines: Vec<String> = Vec::new();
        let mut assume_lines: Vec<String> = Vec::new();
        let mut discharge: Vec<String> = Vec::new();
        let subproof_prefix: Vec<String>;
        let mut nn_lines: Vec<String> = Vec::new();
        let mut nn_ids: Vec<String> = Vec::new();

        let (guards, printed_conclusion) = match &shape {
            Shape::Eval {
                conclusion,
                select,
                value_side,
                read_index,
                path,
                packed_or,
            } => {
                if *packed_or != packed {
                    return None;
                }
                let index_str = self.format_term(*read_index);
                let head = format!("(select {} {index_str})", self.format_term(path.root));
                if self.format_term(*select) != head {
                    return None;
                }
                let tail = self.format_term(*value_side);
                let printed_conclusion = self.format_term(*conclusion);
                let reverse_final = if printed_conclusion == format!("(= {head} {tail})") {
                    false
                } else if printed_conclusion == format!("(= {tail} {head})") {
                    true
                } else {
                    return None;
                };
                let guards = self.row_chain_guards(id, &index_str, &[path])?;
                // A guard-free walk is the depth-1 ROW1 unit lemma, which
                // `ArraySelectStore` already claims; without an assumption
                // there is no subproof to name the closing step.
                if guards.order.is_empty() {
                    return None;
                }
                let mut body: Vec<String> = Vec::new();
                let RowChainPathProof::Step(step) = self.emit_row_chain_path(
                    &guards,
                    RowChainPathEmission {
                        prefix: &format!("{id}.p"),
                        read_index: *read_index,
                        index_str: &index_str,
                        path,
                        tail: &tail,
                    },
                    &mut body,
                )?
                else {
                    return None;
                };
                if reverse_final {
                    body.push(format!(
                        "(step {id}.fin (cl {printed_conclusion}) :rule symm :premises ({step}))"
                    ));
                }
                subproof_prefix = body;
                (guards, printed_conclusion)
            }
            Shape::UnderArrayEq {
                conclusion,
                array_eq_lit,
                eq_term,
                left_target,
                right_target,
                read_index,
                left,
                right,
                packed_or,
            } => {
                if *packed_or != packed {
                    return None;
                }
                let index_str = self.format_term(*read_index);
                let printed_eq = self.format_term(*eq_term);
                let left_str = self.format_term(left.root);
                let right_str = self.format_term(right.root);
                let eq_args = split_application(&printed_eq, "=")?;
                let [printed_left, printed_right] = eq_args.as_slice() else {
                    return None;
                };
                if printed_left != &left_str || printed_right != &right_str {
                    return None;
                }
                if self.format_term(*array_eq_lit) != format!("(not {printed_eq})") {
                    return None;
                }
                let left_head = format!("(select {left_str} {index_str})");
                let right_head = format!("(select {right_str} {index_str})");
                let left_tail = self.format_term(*left_target);
                let right_tail = self.format_term(*right_target);
                let printed_conclusion = self.format_term(*conclusion);
                let derived = format!("(= {left_tail} {right_tail})");
                // A folded Bool conclusion (sub-schema (M): folded (B) or (I)): the
                // term store spelled `(= P b)` as `P` / `(not P)`.
                let folded_bool = folded_bool_closing::folded_bool_conclusion(
                    &left_tail,
                    &right_tail,
                    &printed_conclusion,
                );
                let reverse_final = if printed_conclusion == derived || folded_bool {
                    false
                } else if printed_conclusion == format!("(= {right_tail} {left_tail})") {
                    true
                } else {
                    return None;
                };
                let guards = self.row_chain_guards(id, &index_str, &[left, right])?;
                let heq_id = format!("{id}.h{}", guards.order.len());

                let mut body: Vec<String> = Vec::new();
                let left_proof = self.emit_row_chain_path(
                    &guards,
                    RowChainPathEmission {
                        prefix: &format!("{id}.l"),
                        read_index: *read_index,
                        index_str: &index_str,
                        path: left,
                        tail: &left_tail,
                    },
                    &mut body,
                )?;
                let right_proof = self.emit_row_chain_path(
                    &guards,
                    RowChainPathEmission {
                        prefix: &format!("{id}.r"),
                        read_index: *read_index,
                        index_str: &index_str,
                        path: right,
                        tail: &right_tail,
                    },
                    &mut body,
                )?;
                body.push(format!(
                    "(step {id}.cong (cl (= {left_head} {right_head})) :rule cong :premises ({heq_id}))"
                ));
                let mut trans_premises: Vec<String> = Vec::new();
                if let RowChainPathProof::Step(step) = left_proof {
                    body.push(format!(
                        "(step {id}.ls (cl (= {left_tail} {left_head})) :rule symm :premises ({step}))"
                    ));
                    trans_premises.push(format!("{id}.ls"));
                }
                trans_premises.push(format!("{id}.cong"));
                if let RowChainPathProof::Step(step) = right_proof {
                    trans_premises.push(step);
                }
                if trans_premises.len() > 1 {
                    body.push(format!(
                        "(step {id}.tr (cl (= {left_tail} {right_tail})) :rule trans :premises ({}))",
                        trans_premises.join(" ")
                    ));
                }
                let last = if trans_premises.len() > 1 {
                    format!("{id}.tr")
                } else {
                    format!("{id}.cong")
                };
                if reverse_final {
                    body.push(format!(
                        "(step {id}.fin (cl {printed_conclusion}) :rule symm :premises ({last}))"
                    ));
                }
                if folded_bool {
                    folded_bool_closing::push_folded_bool_closing(
                        &mut body,
                        id,
                        &derived,
                        &printed_conclusion,
                        &last,
                    );
                }
                subproof_prefix = body;
                assume_lines.push(format!("(assume {heq_id} {printed_eq})"));
                discharge.push(heq_id);
                (guards, printed_conclusion)
            }
        };

        // Assumptions come first, in the order the discharge list names them.
        let mut header: Vec<String> = Vec::with_capacity(guards.order.len());
        for (index, printed) in guards.printed.iter().enumerate() {
            header.push(format!(
                "(assume {} (not {printed}))",
                guards.assume_ids[index]
            ));
        }
        header.extend(assume_lines);
        let mut discharge_ids: Vec<String> = guards.assume_ids.clone();
        discharge_ids.extend(discharge);

        // `subproof` negates each assumption in order, so a guard assumed as
        // `(not G)` reappears as `(not (not G))`; `not_not` turns that back
        // into the clause's own positive `G`.
        let mut subproof_clause = String::from("(cl");
        for printed in &guards.printed {
            subproof_clause.push_str(&format!(" (not (not {printed}))"));
        }
        if let Shape::UnderArrayEq { array_eq_lit, .. } = &shape {
            subproof_clause.push(' ');
            subproof_clause.push_str(&self.format_term(*array_eq_lit));
        }
        subproof_clause.push(' ');
        subproof_clause.push_str(&printed_conclusion);
        subproof_clause.push(')');

        for (index, printed) in guards.printed.iter().enumerate() {
            let nn_id = format!("{id}.nn{index}");
            nn_lines.push(format!(
                "(step {nn_id} (cl (not (not (not {printed}))) {printed}) :rule not_not)"
            ));
            nn_ids.push(nn_id);
        }

        lines.push(format!("(anchor :step {id}.sp)"));
        lines.extend(header);
        lines.extend(guards.bridges.iter().cloned());
        lines.extend(subproof_prefix);
        lines.push(format!(
            "(step {id}.sp {subproof_clause} :rule subproof :discharge ({}))",
            discharge_ids.join(" ")
        ));
        lines.extend(nn_lines);
        // With no guards the subproof clause already IS the flat clause up to
        // literal order, and `resolution` needs two premises — restore the
        // original order with `reordering` instead.
        if nn_ids.is_empty() {
            lines.push(format!(
                "(step {flat_id} {} :rule reordering :premises ({id}.sp))",
                self.format_clause(&flat_lits)
            ));
        } else {
            let mut resolution_premises = vec![format!("{id}.sp")];
            resolution_premises.extend(nn_ids);
            lines.push(format!(
                "(step {flat_id} {} :rule resolution :premises ({}))",
                self.format_clause(&flat_lits),
                resolution_premises.join(" ")
            ));
        }

        if let Some(packed_or) = packed {
            let packed_str = self.format_term(packed_or);
            let children = split_application(&packed_str, "or")?;
            if children.len() != flat_lits.len() {
                return None;
            }
            let mut or_neg_ids: Vec<String> = Vec::with_capacity(children.len());
            for (index, (child, &lit)) in children.iter().zip(flat_lits.iter()).enumerate() {
                if child != &self.format_term(lit) {
                    return None;
                }
                let or_id = format!("{id}.o{index}");
                lines.push(format!(
                    "(step {or_id} (cl {packed_str} (not {child})) :rule or_neg :args ({index}))"
                ));
                or_neg_ids.push(or_id);
            }
            let mut premises = vec![flat_id];
            premises.extend(or_neg_ids);
            lines.push(format!(
                "(step {id} (cl {packed_str}) :rule resolution :premises ({}))",
                premises.join(" ")
            ));
        }

        Some(lines.join("\n"))
    }

    /// Build the guard assumptions of a row-chain subproof.
    ///
    /// One assumption per DISTINCT index-equality literal the walks consume,
    /// in first-use order. `arrays_row` demands its premise spell the
    /// disequality as `(not (= store_index read_index))`; a clause carrying
    /// the mirror spelling is bridged with `not_symm`, and any other printed
    /// surface fails closed.
    fn row_chain_guards(
        &self,
        id: ProofId,
        index_str: &str,
        paths: &[&crate::checker::RowChainPath],
    ) -> Option<RowChainGuards> {
        let mut guards = RowChainGuards::default();
        for path in paths {
            for skip in &path.skips {
                if guards.order.contains(&skip.guard) {
                    continue;
                }
                let position = guards.order.len();
                let printed = self.format_term(skip.guard);
                let store_index = self.format_term(skip.store_index);
                let forward = format!("(= {store_index} {index_str})");
                let reverse = format!("(= {index_str} {store_index})");
                let assume_id = format!("{id}.h{position}");
                let row_id = if printed == forward {
                    assume_id.clone()
                } else if printed == reverse {
                    let bridge_id = format!("{id}.s{position}");
                    guards.bridges.push(format!(
                        "(step {bridge_id} (cl (not {forward})) :rule not_symm :premises ({assume_id}))"
                    ));
                    bridge_id
                } else {
                    return None;
                };
                guards.order.push(skip.guard);
                guards.printed.push(printed);
                guards.assume_ids.push(assume_id);
                guards.row_ids.push(row_id);
            }
        }
        Some(guards)
    }

    /// Emit one chain walk's `arrays_row`/`arrays_idx` steps and return the id
    /// of a single step proving `(= (select root index) tail)`.
    ///
    /// `RowChainPathProof::Reflexive` means the walk contributes no step
    /// because `tail` IS `(select root index)` (a base array with no writes).
    /// `None` is the fail-closed answer: the printed surface of some `store`
    /// node is not the compositional rendering of the certified term.
    fn emit_row_chain_path(
        &self,
        guards: &RowChainGuards,
        emission: RowChainPathEmission<'_>,
        lines: &mut Vec<String>,
    ) -> Option<RowChainPathProof> {
        use crate::checker::RowChainEnd;

        if let Some(shared) = self.emit_shared_row_chain_path(guards, &emission, lines) {
            return Some(shared);
        }
        if self.work_budget_exhausted() {
            return None;
        }

        let RowChainPathEmission {
            prefix,
            read_index,
            index_str,
            path,
            tail,
        } = emission;

        let mut step_ids: Vec<String> = Vec::new();
        let mut current = self.format_term(path.root);
        for (position, skip) in path.skips.iter().enumerate() {
            let outer = self.format_term(skip.outer);
            if outer != current {
                return None;
            }
            let inner = self.format_term(skip.inner);
            let store_index = self.format_term(skip.store_index);
            let store_args = split_application(&outer, "store")?;
            let [printed_inner, printed_index, _printed_value] = store_args.as_slice() else {
                return None;
            };
            if printed_inner != &inner || printed_index != &store_index {
                return None;
            }
            let guard_position = guards.order.iter().position(|&g| g == skip.guard)?;
            let step_id = format!("{prefix}{position}");
            lines.push(format!(
                "(step {step_id} (cl (= (select {outer} {index_str}) (select {inner} {index_str}))) \
                 :rule arrays_row :premises ({}))",
                guards.row_ids[guard_position]
            ));
            step_ids.push(step_id);
            current = inner;
        }
        match path.end {
            RowChainEnd::Value { outer, value } => {
                let printed_outer = self.format_term(outer);
                if printed_outer != current {
                    return None;
                }
                let store_args = split_application(&printed_outer, "store")?;
                let [_printed_inner, printed_index, printed_value] = store_args.as_slice() else {
                    return None;
                };
                if printed_index != index_str || printed_value != &self.format_term(value) {
                    return None;
                }
                if printed_value != tail {
                    return None;
                }
                let step_id = format!("{prefix}idx");
                lines.push(format!(
                    "(step {step_id} (cl (= (select {printed_outer} {index_str}) {tail})) \
                     :rule arrays_idx)"
                ));
                step_ids.push(step_id);
            }
            RowChainEnd::Base { base } => {
                let printed_base = self.format_term(base);
                if printed_base != current {
                    return None;
                }
                let canonical_tail = format!("(select {printed_base} {index_str})");
                if tail != canonical_tail {
                    let tail_args = split_application(tail, "select")?;
                    let [tail_base, tail_index] = tail_args.as_slice() else {
                        return None;
                    };
                    if tail_base != &printed_base
                        || !self.is_zero_offset_surface_index(read_index, index_str, tail_index)
                        || la_generic_surface::printed_poly_simp_holds(index_str, tail_index)
                            != Some(true)
                    {
                        return None;
                    }
                    // The strict checker certified this endpoint as the exact
                    // root read at `read_index`.  An authenticated enclosing
                    // select can nevertheless retain the source spelling
                    // `(+ read_index 0)`.  Keep that authored AST and bridge
                    // it explicitly: the polynomial identity proves the index
                    // identity (`poly_simp`; a positive equality is not a
                    // `la_generic` disequality, which the pinned checker
                    // refuses outright), then congruence transports the read.
                    // No surface string is treated as definitionally equal by
                    // the array rule.
                    let index_id = format!("{prefix}bi");
                    let select_id = format!("{prefix}bs");
                    lines.push(format!(
                        "(step {index_id} (cl (= {index_str} {tail_index})) :rule poly_simp)"
                    ));
                    lines.push(format!(
                        "(step {select_id} (cl (= {canonical_tail} {tail})) :rule cong :premises ({index_id}))"
                    ));
                    step_ids.push(select_id);
                }
            }
            // The internal checker re-derives select(const-array(v), i) = v,
            // but the pinned external Alethe checker has no sound primitive
            // for that axiom.  Refuse export instead of spelling it as trust.
            RowChainEnd::Const { .. } => return None,
        }
        match step_ids.len() {
            0 => Some(RowChainPathProof::Reflexive),
            1 => Some(RowChainPathProof::Step(step_ids.remove(0))),
            _ => {
                let head = format!("(select {} {index_str})", self.format_term(path.root));
                let step_id = format!("{prefix}tr");
                lines.push(format!(
                    "(step {step_id} (cl (= {head} {tail})) :rule trans :premises ({}))",
                    step_ids.join(" ")
                ));
                Some(RowChainPathProof::Step(step_id))
            }
        }
    }

    /// Whether an authored arithmetic index is exactly `(+ certified 0)` (or
    /// its commuted spelling).  This is the one surface normalization for
    /// which [`Self::emit_row_chain_path`] emits an explicit `la_generic`
    /// bridge; every other mismatch remains fail-closed.
    fn is_zero_offset_surface_index(
        &self,
        read_index: TermId,
        certified: &str,
        surface: &str,
    ) -> bool {
        if !matches!(self.terms.sort(read_index), Sort::Int | Sort::Real) {
            return false;
        }
        let Some(parts) = split_application(surface, "+") else {
            return false;
        };
        let [left, right] = parts.as_slice() else {
            return false;
        };
        let is_zero = |term: &str| {
            crate::la_generic_signs::parse_numeric_constant(term)
                .is_some_and(|value| value.numer().sign() == Sign::NoSign)
        };
        (left == certified && is_zero(right)) || (right == certified && is_zero(left))
    }

    /// Transport the certified flat ROW theorem onto a packed term whose
    /// surface override spells the AUTHORED implication `(=> (not guard) row)`
    /// rather than AY's internal `(or guard row)`.
    ///
    /// A composed root (`(assert (not (=> (not (= i j)) row)))`) installs that
    /// override so every printed step speaks the problem's own syntax, and the
    /// ROW2 lemma's packed clause term IS that implication. Printing the
    /// override-free or-term here would conclude a term no downstream premise
    /// mentions, so the two premise-free implication tautologies carry the flat
    /// clause across instead:
    ///
    ///   implies_neg1: (cl (=> A B) A)
    ///   implies_neg2: (cl (=> A B) (not B))
    ///
    /// Both are checked by the pinned calculus, so the packed conclusion gains
    /// no authority the flat theorem did not already have. Returns `None`
    /// unless the printed implication is EXACTLY the certified flat clause —
    /// one literal as the consequent and the negation of the other as the
    /// antecedent — so every other surface still fails closed at the caller.
    fn finish_array_packed_implication(
        &self,
        id: ProofId,
        packed: &str,
        flat_id: &str,
        first: &str,
        second: &str,
    ) -> Option<String> {
        let (antecedent, consequent) = split_binary_implies(packed)?;
        let guard = if consequent == second {
            first
        } else if consequent == first {
            second
        } else {
            return None;
        };
        if antecedent != format!("(not {guard})") {
            return None;
        }
        Some(format!(
            "\n(step {id}.i1 (cl {packed} {antecedent}) :rule implies_neg1)\n\
             (step {id}.i2 (cl {packed} (not {consequent})) :rule implies_neg2)\n\
             (step {id}.r0 (cl {guard} {packed}) :rule resolution :premises ({flat_id} {id}.i2))\n\
             (step {id} (cl {packed}) :rule resolution :premises ({id}.r0 {id}.i1))"
        ))
    }

    /// Restore a unit `(or guard row)` when AY's internally checked array
    /// lemma stores the disjunction as one clause term. The flat theorem is
    /// first derived under `flat_id`; two `or_neg` tautologies then introduce
    /// the exact original or-term without changing the premise identity seen
    /// by downstream steps.
    fn finish_array_packed_or(
        &self,
        id: ProofId,
        packed_or: Option<TermId>,
        flat_id: &str,
        first: &str,
        second: &str,
        mut output: String,
    ) -> Result<String, AlethePrintError> {
        let Some(packed_or) = packed_or else {
            return Ok(output);
        };
        let packed = self.format_term(packed_or);
        let Some(children) = split_application(&packed, "or") else {
            if let Some(bridge) =
                self.finish_array_packed_implication(id, &packed, flat_id, first, second)
            {
                output.push_str(&bridge);
                return Ok(output);
            }
            return Err(AlethePrintError::InvalidArrayStep {
                id,
                reason: "packed ROW surface override is no longer an or-term".to_string(),
            });
        };
        let [child0, child1] = children.as_slice() else {
            return Err(AlethePrintError::InvalidArrayStep {
                id,
                reason: "packed ROW or-term must have exactly two children".to_string(),
            });
        };
        if !((child0 == first && child1 == second) || (child0 == second && child1 == first)) {
            return Err(AlethePrintError::InvalidArrayStep {
                id,
                reason: "packed ROW or-term children differ from the certified flat clause"
                    .to_string(),
            });
        }
        let _ = std::fmt::Write::write_fmt(
            &mut output,
            format_args!(
                "\n(step {id}.o0 (cl {packed} (not {child0})) :rule or_neg :args (0))\n\
                 (step {id}.r0 (cl {child1} {packed}) :rule resolution :premises ({flat_id} {id}.o0))\n\
                 (step {id}.o1 (cl {packed} (not {child1})) :rule or_neg :args (1))\n\
                 (step {id} (cl {packed}) :rule resolution :premises ({id}.r0 {id}.o1))"
            ),
        );
        Ok(output)
    }

    /// Rebuild an `eq_transitive` theory-lemma step into spec-valid Alethe
    /// when its printed clause carries `(distinct a b)` hypotheses (AY's
    /// surface spelling of `(not (= a b))`) or degenerates to the two-literal
    /// symmetry tautology (`(cl (not (= a b)) (= b a))`, which Carcara rejects
    /// because `eq_transitive` needs at least two hypotheses).
    ///
    /// The rebuilt derivation:
    ///   {id}.et  — `eq_transitive` over the canonical `(not (= …))` forms,
    ///              with a reflexive filler hypothesis in the degenerate case;
    ///   {id}.rfl — `eq_reflexive` unit for that filler (degenerate case only);
    ///   {id}.d_k/{id}.q_k — `distinct_elim` + `equiv2`, one pair per printed
    ///              `(distinct …)` hypothesis, producing `(cl (distinct a b)
    ///              (not (not (= a b))))`;
    ///   {id}     — a `resolution` cancelling each canonical hypothesis against
    ///              its bridge (and the filler against {id}.rfl), yielding the
    ///              ORIGINAL printed clause byte-for-byte.
    ///
    /// Returns `None` for an already-spec-valid `eq_transitive` (≥3 literals,
    /// no `distinct` hypothesis) so those steps stay byte-identical, and for
    /// any clause whose shape it does not recognise (fall back to the faithful
    /// — if unchecked — rule name rather than emit an unsound rewrite).
    fn resugar_eq_transitive(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        // Printed + canonical (`(not (= a b))`) form of each literal, plus the
        // `(a, b)` operands when the literal printed in `(distinct a b)` form.
        struct LitInfo {
            printed: String,
            canonical: String,
            distinct: Option<(String, String)>,
            is_conclusion: bool,
        }
        let mut infos: Vec<LitInfo> = Vec::with_capacity(clause.len());
        for &lit in clause {
            let printed = self.format_term(lit);
            if let Some(ops) = split_application(&printed, "distinct") {
                let [a, b] = ops.as_slice() else {
                    return None;
                };
                infos.push(LitInfo {
                    canonical: format!("(not (= {a} {b}))"),
                    distinct: Some((a.clone(), b.clone())),
                    is_conclusion: false,
                    printed,
                });
            } else {
                let is_conclusion = printed.starts_with("(= ");
                infos.push(LitInfo {
                    canonical: printed.clone(),
                    distinct: None,
                    is_conclusion,
                    printed,
                });
            }
        }

        let n = infos.len();
        let distinct_count = infos.iter().filter(|i| i.distinct.is_some()).count();
        // Already spec-valid: a ≥3-literal chain with no `distinct` hypothesis.
        // Leave it byte-identical.
        if distinct_count == 0 && n >= 3 {
            return None;
        }
        // Only touch the exact eq_transitive shape: exactly one positive
        // equality conclusion, every other literal a negated equality.
        if n < 2 {
            return None;
        }
        let conclusion_count = infos.iter().filter(|i| i.is_conclusion).count();
        if conclusion_count != 1 {
            return None;
        }
        for info in &infos {
            if !info.is_conclusion
                && !info.canonical.starts_with("(not (= ")
                && info.distinct.is_none()
            {
                return None;
            }
        }

        let mut out = String::new();
        // Build the canonical `eq_transitive` hypothesis clause.
        let mut premises: Vec<String> = vec![format!("{id}.et")];
        if n == 2 {
            // Degenerate symmetry tautology `(cl (not (= a b)) (= b a))`.
            // Pad with a reflexive hypothesis on the conclusion's second
            // operand so the chain has two hypotheses.
            let concl = infos.iter().find(|i| i.is_conclusion)?;
            let concl_ops = split_application(&concl.printed, "=")?;
            let [_, s] = concl_ops.as_slice() else {
                return None;
            };
            let hyp = infos.iter().find(|i| !i.is_conclusion)?;
            let refl_hyp = format!("(not (= {s} {s}))");
            // The padded clause is what {id}.et ships; judge it the same way
            // the un-resugared path is judged, over that exact text.
            if !eq_transitive::printed_eq_transitive_chain_holds(&[
                hyp.canonical.as_str(),
                refl_hyp.as_str(),
                concl.printed.as_str(),
            ]) {
                return None;
            }
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id}.et (cl {} {} {}) :rule eq_transitive)\n",
                    hyp.canonical, refl_hyp, concl.printed
                ),
            );
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!("(step {id}.rfl (cl (= {s} {s})) :rule eq_reflexive)\n"),
            );
            premises.push(format!("{id}.rfl"));
        } else {
            let canon: Vec<&str> = infos.iter().map(|i| i.canonical.as_str()).collect();
            // Resugaring `(distinct a b)` back to `(not (= a b))` restores the
            // shape `eq_transitive` wants but says nothing about the chain.
            // Judge the canonical clause before claiming the rule over it.
            if !eq_transitive::printed_eq_transitive_chain_holds(&canon) {
                return None;
            }
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id}.et (cl {}) :rule eq_transitive)\n",
                    canon.join(" ")
                ),
            );
        }

        // One `distinct_elim` + `equiv2` bridge per printed `(distinct …)`
        // hypothesis, converting `(not (= a b))` back into `(distinct a b)`.
        for (k, info) in infos.iter().enumerate() {
            let Some((a, b)) = &info.distinct else {
                continue;
            };
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id}.d{k} (cl (= (distinct {a} {b}) (not (= {a} {b})))) \
                     :rule distinct_elim)\n\
                     (step {id}.q{k} (cl (distinct {a} {b}) (not (not (= {a} {b})))) \
                     :rule equiv2 :premises ({id}.d{k}))\n"
                ),
            );
            premises.push(format!("{id}.q{k}"));
        }

        // Final resolution reproduces the ORIGINAL printed clause exactly.
        let printed_clause: Vec<&str> = infos.iter().map(|i| i.printed.as_str()).collect();
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl {}) :rule resolution :premises ({}))",
                printed_clause.join(" "),
                premises.join(" ")
            ),
        );
        Some(out)
    }

    /// Render a fresh-symbol definitional bound.
    ///
    /// Unlike `array_ext_diff_intro`, this step carries a clause that later
    /// steps resolve against and therefore cannot be demoted to a comment.
    ///
    /// There is no Alethe rule for it. Alethe has no notion of a solver
    /// introducing a symbol and defining it, and the two rules that come
    /// closest are not it: `la_generic` would claim `(<= d lin)` is a rational
    /// tautology (it is FALSE at `d = lin + 1`), and `sko_ex` would claim the
    /// symbol is a `choice` term it is not. So the honest wire rule is `hole`
    /// — exactly what the premiseless `trust` this replaces already printed,
    /// which is why the emitted document is unchanged by that lane.
    ///
    /// The `:args` MUST be dropped: the pinned carcara build rejects `hole`
    /// arguments, turning a `holey` document into an `invalid` one. AY's checker
    /// re-derives the defined symbol from the step, so omitting it loses nothing.
    fn format_fresh_def_bound(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        crate::checker::validate_fresh_definition_for_printer(
            self.terms,
            &ay_core::AletheRule::FreshDefBound,
            id,
            clause,
            premises,
            args,
        )
        .map_err(|err| AlethePrintError::InvalidSurfaceStep {
            id,
            reason: err.to_string(),
        })?;
        let clause_str = self.format_clause(clause);
        Ok(format!(
            "(step {id} {clause_str} :rule {})",
            ay_core::UNPROVED_STEP_RULE
        ))
    }

    /// `fresh_def_eq` lowers exactly as `fresh_def_bound` does, and for the
    /// same two reasons: there is no Alethe rule for a solver introducing a
    /// symbol and defining it, and the `:args` MUST be dropped because the
    /// pinned carcara build rejects `hole` arguments outright (turning a
    /// `holey` document into an `invalid` one — strictly worse than the
    /// premiseless `trust` this step replaces, which prints the same text).
    ///
    /// The near-miss worth naming for THIS rule specifically: `eq_congruent`
    /// and `refl` are both `=`-shaped and both would render, and both would be
    /// FALSE claims — `(= d expr)` is not reflexive and is not a congruence of
    /// anything. `hole` is the only honest wire.
    fn format_fresh_def_eq(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        crate::checker::validate_fresh_definition_for_printer(
            self.terms,
            &ay_core::AletheRule::FreshDefEq,
            id,
            clause,
            premises,
            args,
        )
        .map_err(|err| AlethePrintError::InvalidSurfaceStep {
            id,
            reason: err.to_string(),
        })?;
        let clause_str = self.format_clause(clause);
        Ok(format!(
            "(step {id} {clause_str} :rule {})",
            ay_core::UNPROVED_STEP_RULE
        ))
    }

    /// `divmod_def` lowers exactly as the other fresh definitions do, for the
    /// same reasons: no Alethe rule introduces and defines a symbol, and the
    /// pinned carcara build rejects `hole` arguments.
    fn format_divmod_def(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        crate::checker::validate_fresh_definition_for_printer(
            self.terms,
            &ay_core::AletheRule::DivModDef,
            id,
            clause,
            premises,
            args,
        )
        .map_err(|err| AlethePrintError::InvalidSurfaceStep {
            id,
            reason: err.to_string(),
        })?;
        let clause_str = self.format_clause(clause);
        Ok(format!(
            "(step {id} {clause_str} :rule {})",
            ay_core::UNPROVED_STEP_RULE
        ))
    }

    fn format_generic_step(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        if matches!(rule, ay_core::AletheRule::BvReconstructV1) {
            return clean_bitvec_rules::format_bv_reconstruct(self, id, clause, premises, args);
        }
        if matches!(rule, ay_core::AletheRule::BvOffsetSpinesV1) {
            return clean_bitvec_rules::format_bv_offset_spines(self, id, clause, premises, args);
        }
        if matches!(rule, ay_core::AletheRule::EqSimplify) {
            crate::checker::bv_eq_simplify::validate(
                self.terms,
                id,
                clause,
                premises.len(),
                args.len(),
                &mut |_, _| true,
            )
            .map_err(|error| AlethePrintError::InvalidSurfaceStep {
                id,
                reason: error.to_string(),
            })?;
            let clause_str = self.format_clause(clause);
            if dialect::current() == dialect::AletheDialect::PinnedCarcara {
                return Ok(format!("(step {id} {clause_str} :rule hole)"));
            }
            let wire_overrides = self.judgement_overrides();
            if !crate::bv_eq_simplify_step_lowering_supported(
                dialect::current(),
                self.terms,
                clause,
                premises.len(),
                args.len(),
                wire_overrides.as_ref(),
            ) {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "BV equality simplification changed under surface rewriting"
                        .to_string(),
                });
            }
            dialect::note_clean_only(dialect::CleanOnlySpelling::BvOffsetEqualitySimplify);
            return Ok(format!("(step {id} {clause_str} :rule eq_simplify)"));
        }
        if matches!(rule, ay_core::AletheRule::ForallInst) {
            if let Some(text) = self.format_confined_forall_inst(id, clause) {
                return Ok(text);
            }
        }
        if matches!(rule, ay_core::AletheRule::Trans) {
            let proof_clauses = self.proof_clauses.borrow();
            let Some(premise_clauses) = premises
                .iter()
                .map(|premise| proof_clauses.get(premise).map(Vec::as_slice))
                .collect::<Option<Vec<_>>>()
            else {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "trans step references an unavailable premise clause".to_string(),
                });
            };
            let wire_overrides = self.judgement_overrides();
            if !trans_step_surface_is_supported(
                self.terms,
                clause,
                &premise_clauses,
                wire_overrides.as_ref(),
            ) {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "transitivity chain changed under surface rewriting".to_string(),
                });
            }
        }
        let evaluate_supported = if matches!(rule, ay_core::AletheRule::Evaluate) {
            let wire_overrides = self.judgement_overrides();
            crate::evaluate_step_lowering_supported(self.terms, clause, wire_overrides.as_ref())
        } else {
            true
        };
        if !evaluate_supported {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "evaluate conclusion changed under surface rewriting".to_string(),
            });
        }
        if matches!(rule, ay_core::AletheRule::Evaluate) {
            if let Some(text) =
                self.format_negative_value_evaluate(id, clause, &self.format_clause(clause))
            {
                return Ok(text);
            }
        }
        if matches!(rule, ay_core::AletheRule::FreshDefBound) {
            return self.format_fresh_def_bound(id, clause, premises, args);
        }
        if matches!(rule, ay_core::AletheRule::FreshDefEq) {
            return self.format_fresh_def_eq(id, clause, premises, args);
        }
        if matches!(rule, ay_core::AletheRule::DivModDef) {
            return self.format_divmod_def(id, clause, premises, args);
        }
        if surface_symm::is_symmetry_rule(rule) {
            return self.format_surface_symm(id, rule, clause, premises, args);
        }
        // `eq_transitive` is `trans`'s premise-FREE twin and needs the same
        // discipline `trans_step_surface_is_supported` already gives `trans`:
        // the chain is a relation among the printed operands, and the surface
        // override channel re-spells those independently of the term DAG. AY's
        // own checker re-derives the chain over the term store and is right to
        // accept it; the document the external checker reads is a different
        // object. Decline to the honest `hole` rather than claim a rule the
        // shipped text does not instantiate.
        if matches!(rule, ay_core::AletheRule::EqTransitive)
            && !self.eq_transitive_prints_spec_valid(clause)
        {
            return Ok(self.eq_transitive_bridged_or_hole(id, clause));
        }
        // `eq_congruent_pred` is the same kind of premise-free relation over
        // its printed operands (argument pair `i` against hypothesis `i`), and
        // was the one such rule left unjudged by the 2026-09-11 audit.
        if matches!(rule, ay_core::AletheRule::EqCongruentPred)
            && !self.eq_congruent_pred_prints_spec_valid(clause)
        {
            return Ok(self.eq_congruent_pred_chain_or_hole(id, clause));
        }
        // `forall_inst` is syntactic: the checker substitutes the printed
        // `:args` into the printed quantifier's body and asks whether the
        // printed instance is that image. The instance and the arguments
        // reach the wire through different rendering channels (the
        // producer's override table for the one, this printer's Skolem
        // `choice` table for the other), so the same `TermId` can ship two
        // spellings and the term-level validator cannot see it. Judge the
        // text; decline to the honest hole.
        if matches!(rule, ay_core::AletheRule::ForallInst) {
            let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
            let printed_args: Vec<String> = args.iter().map(|&arg| self.format_term(arg)).collect();
            let borrowed: Vec<&str> = printed_args.iter().map(String::as_str).collect();
            let holds = match printed.as_slice() {
                [literal] => quantifier_surface::printed_forall_inst_holds(literal, &borrowed),
                _ => false,
            };
            if !holds {
                return Ok(format!(
                    "(step {id} {} :rule {})",
                    self.format_clause(clause),
                    ay_core::UNPROVED_STEP_RULE
                ));
            }
        }
        let is_resolution = resolution_args::is_generic_resolution(rule);
        if is_resolution {
            resolution_args::validate_generic_resolution_args(self.terms, premises.len(), args)
                .map_err(|reason| AlethePrintError::InvalidSurfaceStep { id, reason })?;
        }
        if premises.len() == 2 && is_resolution {
            if let Some(text) =
                self.distinct_eq_resolution_bridge(id, clause, premises[0], premises[1])
            {
                return Ok(text);
            }
            if self.surface_resolution_needs_distinct_bridge(
                clause,
                args.first().copied(),
                premises[0],
                premises[1],
            ) {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "a printed distinct/equality pivot cannot be bridged to the authored operands"
                        .to_string(),
                });
            }
        }
        // The conclusion a judged resolution ships, rendered once and carried
        // to the default rendering below.
        let mut judged_clause_str: Option<String> = None;
        if is_resolution {
            resolution_args::validate_generic_resolution_surface(self, clause, premises, args)
                .map_err(|reason| AlethePrintError::InvalidSurfaceStep { id, reason })?;
            // `validate_generic_resolution_surface` returns early on an
            // argument-FREE step: with no `:args` there is no annotation to
            // validate, and no judgement read exactly like approval — which is
            // how the `th_resolution` false green reached the wire. Judge the
            // printed text instead, for annotated and bare steps alike.
            let clause_str = self.format_clause(clause);
            if let Some(text) = self.judge_printed_resolution(id, clause, &clause_str, premises)? {
                return Ok(text);
            }
            judged_clause_str = Some(clause_str);
        }
        // A comparison may carry the authored `>=`/`>` spelling while its
        // canonical internal term is the equivalent argument-reversed
        // `<=`/`<` application. If that term is the left side of a `cong`
        // conclusion, the global override would otherwise make the printed
        // applications have different operators. Re-establish the canonical
        // application with `comp_simplify`, apply same-operator congruence,
        // then compose the equalities.
        if matches!(rule, ay_core::AletheRule::Cong) {
            if let Some(text) = self.zero_extend_zero_cong_bridge(id, clause, premises, args)? {
                return Ok(text);
            }
            match self.surface_ac_cong_bridge(id, clause, premises, args) {
                Ok(Some(text)) => return Ok(text),
                Ok(None) => {}
                Err(reason) => {
                    return Err(AlethePrintError::InvalidCongruenceStep { id, reason });
                }
            }
            if let Some(text) = self.surface_order_cong_bridge(id, clause, premises, args) {
                return Ok(text);
            }
            if let Some(text) =
                self.surface_order_cong_bridge_either_side(id, clause, premises, args)
            {
                return Ok(text);
            }
            if let Some(text) = self.head_respelled_cong_bridge(id, clause, premises, args) {
                return Ok(text);
            }
            if self.surface_cong_has_different_order_operators(clause) {
                return Err(AlethePrintError::InvalidCongruenceStep {
                    id,
                    reason: "surface rewriting gives the two congruence applications different order operators"
                        .to_string(),
                });
            }
            // The general shape-changing case. A surface override may
            // re-render an internal term as the SOURCE text it was simplified
            // from — e.g. the internal `(<= a b)` prints back as the authored
            // `(and (<= a b) (<= c c))` it was simplified out of. The internal
            // congruence is a perfectly good same-operator inference, but the
            // PRINTED step equates an `and` with a `<=`, and the default
            // rendering below would ship it.
            //
            // There is no honest repair. Stating the surface equality as a
            // `hole` and composing with `trans` would turn `invalid` into
            // `holey` while proving NOTHING about the two terms — a hole
            // proves anything, so a holey verdict bought that way hides the
            // defect instead of reporting it, which is strictly worse than
            // `invalid`. DECLINE, and let the caller's unverifiable-proof path
            // fire.
            if let Some(reason) = self.surface_cong_has_uncheckable_operands(clause) {
                return Err(AlethePrintError::InvalidCongruenceStep { id, reason });
            }
        }
        if matches!(rule, ay_core::AletheRule::EqCongruent) {
            match self.surface_eq_congruent_bridge(id, clause, premises, args) {
                Ok(Some(text)) => return Ok(text),
                Ok(None) => {}
                Err(reason) => {
                    return Err(AlethePrintError::InvalidCongruenceStep { id, reason });
                }
            }
            if let Some(text) = self.format_indexed_eq_congruent(id, clause, premises, args) {
                return Ok(text);
            }
            // Same judgement as the theory-lemma path: a premise-free,
            // argument-free `eq_congruent` rule step is spelled, rendered
            // byte-identically or holed over the text it ships, never left
            // to the default rendering under a rule name the printed clause
            // may not instantiate (the OR-packed unit, the omitted
            // identical-argument position, a re-spelled hypothesis).
            if premises.is_empty() && args.is_empty() {
                if let Some(text) = self.format_eq_congruent_or_hole(id, clause) {
                    return Ok(text);
                }
            }
        }
        if let Some(text) = self.format_conjunctive_implies_pos(id, rule, clause, premises, args)? {
            return Ok(text);
        }
        // Surface-syntax implication resugar: elaboration desugars
        // `(=> a b)` to `(or (not a) b)` and Tseitin annotates the
        // tautology as or_pos/or_neg over the or-term — but the printed
        // proof renders that term with its surface override `(=> a b)`
        // (so `assume` steps match the input problem). An or_pos step
        // over a printed implication is not spec-valid Alethe; the
        // spec-correct rules for the surface connective are:
        //   implies_pos:  (cl (not (=> A B)) (not A) B)
        //   implies_neg1: (cl (=> A B) A)
        //   implies_neg2: (cl (=> A B) (not B))
        if premises.is_empty() {
            if let Some(text) = self.resugar_implies_tautology(id, rule, clause, args) {
                return Ok(text);
            }
            // Equality-split extraction: elaboration lowers an arithmetic
            // equality `(= L R)` to the conjunction `(and (<= ..) (<= ..))`
            // (printed back as `(= L R)` via its surface override) and
            // Tseitin annotates the one-sided extraction as `and_pos` — but
            // `and_pos` over a printed equality is not spec-valid Alethe.
            // The spec-correct rule for the printed shape is a certified
            // `la_generic` orientation lemma (#relu-trust-glue).
            if let Some(text) = self.resugar_equality_split_and_pos(id, rule, clause) {
                return Ok(text);
            }
            if let Some(text) = self.resugar_and_pos_false_or_and(id, rule, clause, args) {
                return Ok(text);
            }
            // `and_pos` whose `(not (and ...))` gate literal was traced as its
            // De Morgan surface `(or (not A1) .. (not An))`: re-slot to the
            // spec-shaped `(cl (not (and ...)) Ak)` Carcara requires.
            if let Some(text) = self.resugar_and_pos_not_and(id, rule, clause, args) {
                return Ok(text);
            }
            if matches!(rule, ay_core::AletheRule::AndPos(_)) {
                // Canonicalization can flatten `not (A => B)` to an AND, but
                // that effective source needs a multi-rule implication bridge
                // rather than a direct positional projection. Keep this
                // specialized derivation ahead of the ordinary flat-AND gate.
                if let [source] = args {
                    let source_surface = self.format_term(*source);
                    if let Some(text) = self.format_not_implies_and_pos(id, clause, &source_surface)
                    {
                        return Ok(text);
                    }
                }
            }
            // The specialized `and_pos` bridges above format their candidate
            // source/gate before deciding whether they apply. Once that work
            // exhausts the shared budget, `format_term` deliberately returns
            // a private placeholder. Do not let the surface-shape guards below
            // misclassify that placeholder as malformed input. `or_pos` is in
            // the same position now that its guard reads the printed surface
            // rather than failing open on it.
            if matches!(
                rule,
                ay_core::AletheRule::AndPos(_) | ay_core::AletheRule::OrPos(_)
            ) && self.work_budget_exhausted()
            {
                return Err(self.work_budget_error(id.0));
            }
            // `or_pos` whose printed gate is a NESTED binary `or` while the
            // internal or-term is n-ary: carcara compares the gate's TOP-LEVEL
            // arity against the clause tail length, so a re-nested surface
            // spelling is rejected ("expected 6 terms in 'or' term, got 2").
            if let Some(text) = self.resugar_or_pos_nested(id, rule, clause, args) {
                return Ok(text);
            }
            // Clausification tautologies over a source term whose PRINTED
            // form diverges from the internal canonical form (surface-syntax
            // overrides reordering commutative arguments, `=>` desugared to
            // an or-term) — or whose traced literals were double-negation
            // stripped (`a` where strict Alethe wants `(not (not a))`) —
            // are re-derived from the printed operands: the spec-shaped
            // tautology, `not_not` bridge steps for each stripped literal,
            // and a final resolution restoring the exact traced clause.
            //
            // The verdict is KEPT rather than discarded: `NoMatch` is the only
            // evidence the printer has that the default rendering below is not
            // a spec instance of the rule it names, and dropping it is exactly
            // how the `or_pos` De Morgan defect shipped.
            let mut surface_tautology = SurfaceTautology::Unjudged;
            if !matches!(rule, ay_core::AletheRule::AndPos(_)) {
                surface_tautology = self.format_surface_tautology(id, rule, clause, args);
                if let SurfaceTautology::Rendered(text) = surface_tautology {
                    return Ok(text);
                }
            }
            if matches!(rule, ay_core::AletheRule::AndPos(_))
                && clause.iter().copied().any(|literal| {
                    let TermData::Not(source) = self.terms.get(literal) else {
                        return false;
                    };
                    matches!(
                        self.terms.get(*source),
                        TermData::App(Symbol::Named(name), _) if name == "and"
                    ) && split_application(&self.format_term(*source), "and").is_none()
                })
            {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: "and_pos source no longer prints as an and-term and no certified surface bridge applies"
                        .to_string(),
                });
            }
            // DECLINE the two printed-shape defects this pass repairs.
            // Reaching here means every certified bridge declined, so the
            // DEFAULT rendering below is about to ship a step carcara rejects:
            //   * `and_pos` whose gate literal is the De Morgan or-form — the
            //     23-instance census class ("term '(or ..)' is of the wrong
            //     form, expected '(not(and ...))'");
            //   * `or_pos` whose printed gate arity differs from the clause
            //     tail ("expected 6 terms in 'or' term, got 2").
            //
            // THE FLOOR, and why this is not a `raise`. A wrong proof is worse
            // than no proof, but neither is the choice here: the step is
            // PREMISE-FREE, so declining it to the honest `hole` over its own
            // clause leaves every premise reference in the document intact and
            // says exactly what is true — AY holds the derivation, the printer
            // has no spelling of it the pinned checker reads. Raising instead
            // refuses the WHOLE EXPORT, and MEASURED 2026-09-17 on today's main
            // (a3772363b3, build 10168) that is what it does: QF_UF
            // `QG-classification/qg5/iso_icl1206` reaches this guard at `t405`
            // with `or_pos printed gate arity 2 ... clause tail length 5`, and
            // main emits NO certificate where 7c84c9044d — one day older and
            // with this same guard in it — publishes a 14.8 MB document the
            // pinned checker calls `holey` with zero refused steps. The
            // producer's shape moved under the guard; the guard's failure mode
            // turned that into a withdrawn document. Same doctrine as
            // `surface_and_pos`'s floor (061e437f66) and
            // `judge_printed_resolution`'s (79d0bb91bb): an honest hole in a
            // published document, never a dropped certificate.
            //
            // THE FLOOR HAS A FLOOR, and it is the printed clause's own truth
            // (2026-09-17, second pass). `unrepairable_gate_reason` fires on
            // three populations and only two of them are safe to hole:
            //
            //   * a gate whose printed disjuncts are all traced literals — the
            //     printed arity is merely smaller than the tail, or one leaf is
            //     the other orientation of a symmetric `=`. Its clause is a
            //     tautology over the printed text, so `hole` says exactly what
            //     is true and the document is published. `iso_icl1206`'s `t405`
            //     is in here.
            //   * a gate whose printed source was RESPELLED by the surface
            //     override channel into a term with no relation to the tail
            //     (`(not (= p q)) a b`), or whose printed disjunction still
            //     quotes a disjunct the traced clause pruned
            //     (`(not (or a b c)) a b`). Those printed clauses are FALSE.
            //     MEASURED 2026-09-17 on `3b89e303c5`: the floor emitted all
            //     three, and a document whose only unchecked step is
            //     `(cl (not (or a b c)) a b)` refutes a SATISFIABLE problem
            //     with pinned carcara answering `holey`, exit 0. A hole claims
            //     nothing only when its clause is true; a false hole launders a
            //     false lemma past a checker that does not look at it, which is
            //     strictly worse than the `invalid` the guard exists to stop —
            //     the same reasoning `surface_cong_has_uncheckable_operands`
            //     already applies one screen up.
            //
            // So: certify the printed clause or DECLINE THE DOCUMENT. The
            // certificate is sound and incomplete, which puts every
            // incompleteness on the decline side.
            if let Some(reason) = self.unrepairable_gate_reason(rule, clause, args) {
                let printed: Vec<String> =
                    clause.iter().map(|&lit| self.format_term(lit)).collect();
                self.charge(printed.iter().map(|lit| lit.len() as u64).sum());
                if self.work_budget_exhausted() {
                    return Err(self.work_budget_error(id.0));
                }
                if printed_validity::printed_clause_is_certainly_valid(&printed) {
                    if ay_core::misc_cli_flags().debug_cert {
                        ay_core::safe_eprintln!("c !! unrepairable gate at {id}: hole ({reason})");
                    }
                    return Ok(self.printed_hole(id, clause));
                }
                if ay_core::misc_cli_flags().debug_cert {
                    ay_core::safe_eprintln!(
                        "c !! unrepairable gate at {id}: DECLINE, printed clause not certified \
                         ({reason})"
                    );
                }
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: format!(
                        "{reason}, and the printed clause is not a tautology over the printed \
                         text, so a hole would publish a false claim"
                    ),
                });
            }
            // THE GENERAL FORM of the two guards above, on the PRINTED TEXT.
            //
            // `and_pos` and `or_pos` each got a hand-written guard after a
            // defect shipped under them. Both defects were the same shape and
            // neither rule is special: a premise-free "tautologous rule" is
            // valid or not purely as a function of the printed clause and the
            // printed source term, and the surface override channel can move
            // that text out from under ANY of them. `format_surface_tautology`
            // already decides exactly that question — it instantiates the
            // rule's spec template over the PRINTED operands and compares
            // against the PRINTED literals — but its answer was previously
            // thrown away when it did not produce replacement text.
            //
            // `NoMatch` therefore means: every spec template for this rule was
            // tried against the printed surface and none reproduces the clause,
            // so the default rendering is about to claim a rule the printed
            // step does not instantiate. Fail loud. `Unjudged` (rule outside
            // the family, no identifiable source term, exhausted work budget)
            // changes nothing, and `DefaultIsExact` falls through to the
            // byte-identical default on purpose.
            if matches!(surface_tautology, SurfaceTautology::NoMatch) {
                return Err(AlethePrintError::InvalidSurfaceStep {
                    id,
                    reason: format!(
                        "no {rule} instance over the printed surface reproduces this clause, \
                         and no certified printed-shape bridge applies"
                    ),
                });
            }
        }
        // Every remaining `and_pos` is owned by the exact flat-surface gate.
        // Calling it outside the premise-free block is deliberate: malformed
        // copied/generic steps with premises must reject rather than falling
        // through to an invalid default wire rule.
        if let Some(text) = self.format_flat_surface_and_pos(id, rule, clause, premises, args)? {
            return Ok(text);
        }
        // An `or` decomposition step whose premise assume PRINTS as a
        // right-associated implication chain is not spec-valid Alethe over
        // the printed premise. Rebuild it from premiseless `implies_pos`
        // tautologies and an n-ary resolution against the authored assume.
        if matches!(rule, ay_core::AletheRule::Or) && premises.len() == 1 {
            match self.resugar_implies_decomposition(id, clause, premises[0]) {
                Ok(Some(text)) => return Ok(text),
                Ok(None) => {}
                Err(reason) => {
                    return Err(AlethePrintError::InvalidSurfaceStep { id, reason });
                }
            }
            // The analogous De Morgan surface form `(not (and A1 .. An))`
            // needs the spec-correct `not_and` rule instead.
            if let Some(text) = self.resugar_not_and_decomposition(id, clause, premises[0]) {
                return Ok(text);
            }
            // The premise decomposes fine, but the conclusion states an order
            // atom in the other of its two spellings. Same defect as the
            // premise-free family, on the other side of the premise line.
            if let Some(text) = self.reorient_or_decomposition(id, clause, premises[0]) {
                return Ok(text);
            }
        }
        // carcara's `or` rule is POSITIONAL: it zips the premise or-term's
        // disjuncts against the conclusion's literals and requires them equal
        // pairwise. MEASURED on carcara 1.1.0: premise `(or a b)` with
        // conclusion `(cl b a)` is
        // `checking failed on step 't1' with rule 'or': expected terms to be
        // equal: 'a' and 'b'`, while `(cl a b)` is accepted. It does NOT
        // flatten either — a nested or-term gives "expected 2 terms in clause,
        // got 3".
        //
        // AY's internal clause is a SET: its `Vec<TermId>` order is whatever
        // order the solver happened to build the clause in, i.e. a permutation
        // of the disjuncts in general. Reordering a `cl` is sound (an Alethe
        // clause IS a disjunction) and touches only the RENDERING: the proof
        // object, its premises, and AY's own checker all see the same clause.
        // Fires only when the printed literals are an exact permutation of the
        // printed disjuncts, so every other `or` step stays byte-identical.
        let reordered_or_clause;
        let clause = if matches!(rule, ay_core::AletheRule::Or) && premises.len() == 1 {
            match self.or_conclusion_in_premise_order(clause, premises[0]) {
                Some(reordered) => {
                    reordered_or_clause = reordered;
                    reordered_or_clause.as_slice()
                }
                None => clause,
            }
        } else {
            clause
        };
        // A resolution's clause is the one its judgement read (the `or`
        // reordering above and the resolution judgement are on disjoint
        // rules); everything else renders here.
        let clause_str = judged_clause_str.unwrap_or_else(|| self.format_clause(clause));
        // WIRE name, not `Display`/`AletheRule::name()`. Every surface
        // resugaring that produces a genuine Alethe inference has already
        // returned above; the default rendering must not put a rule name the
        // checker does not implement on the wire, because that is not a weaker
        // proof — it is *no* proof (carcara: `UnknownRule` => `invalid`).
        // `AletheRule::Trust` and the theory-specific names with no Alethe
        // counterpart become `hole` here, which checks as *holey*.
        // ... and a name that IS real is still only allowed when this step is
        // an instance of it (see `wire_rule_for_printed_step`).
        let wire =
            Self::wire_rule_for_printed_step(rule.wire_name(), &clause_str, premises.is_empty());
        // Same last-chance lowering the theory-lemma path gets: a premise-free
        // ground bitvector disequality is re-derivable by the checker itself
        // (`evaluate` + `equiv1` + `false` + `resolution`). Premise-carrying
        // steps are excluded because the replacement re-derives the clause
        // from nothing and would silently drop those premises.
        if wire == ay_core::UNPROVED_STEP_RULE && premises.is_empty() && args.is_empty() {
            if let Some(text) = Self::lower_ground_bv_disequality(id, &clause_str) {
                return Ok(text);
            }
            if let Some(text) = self.lower_closed_boolean_clause(id, &clause_str) {
                return Ok(text);
            }
        }
        // Carcara reads an `evaluate` value only as a literal; the printed
        // `(- 4)` is joined to `-4` by `refl` (`evaluate_literal`).
        if wire == "evaluate" && premises.is_empty() && args.is_empty() {
            return Ok(self.format_evaluate_step(id, clause, &clause_str));
        }
        let mut result = format!("(step {id} {clause_str} :rule {wire}");
        if !premises.is_empty() {
            let premises_str: Vec<String> = premises.iter().map(ToString::to_string).collect();
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :premises ({})", premises_str.join(" ")),
            );
        }
        if let Some(args_str) = self.format_external_args(rule, clause, premises, args) {
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :args ({})", args_str.join(" ")),
            );
        }
        result.push(')');
        Ok(result)
    }

    /// Repair the exact surface-normalization shape
    ///
    /// ```text
    /// internal: (= (<= k x) (<= k y))
    /// printed:  (= (>= x k) (<= k y))
    /// ```
    ///
    /// A direct printed `cong` is invalid because its applications have
    /// different operators. The bridge proves the authored/canonical
    /// comparison equality with `comp_simplify`, retains the original
    /// same-operator `cong`, and joins them with `trans`.
    ///
    /// This is deliberately fail-closed: it applies only to one positive unit
    /// equality, one unit-equality premise over the differing internal pair
    /// (whose printed spelling may differ only by a certified multiplication
    /// commutation), exactly one differing application argument, and an exact
    /// argument-reversed order override on the conclusion's left side. Every
    /// other `cong` remains byte-unchanged.
    fn surface_order_cong_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        let [premise] = premises else {
            return None;
        };
        if !args.is_empty() {
            return None;
        }

        let overrides = self.term_overrides?;
        if overrides.contains_key(conclusion) {
            return None;
        }
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(*conclusion) else {
            return None;
        };
        if eq != "=" {
            return None;
        }
        let [left, right] = equality_args.as_slice() else {
            return None;
        };
        if overrides.contains_key(right) {
            return None;
        }
        let uses_skolem_override = {
            let skolem_overrides = self.skolem_overrides.borrow();
            skolem_overrides.contains_key(conclusion)
                || skolem_overrides.contains_key(left)
                || skolem_overrides.contains_key(right)
        };
        if uses_skolem_override {
            return None;
        }

        let TermData::App(left_symbol, left_args) = self.terms.get(*left) else {
            return None;
        };
        let TermData::App(right_symbol, right_args) = self.terms.get(*right) else {
            return None;
        };
        if left_symbol != right_symbol {
            return None;
        }
        let Symbol::Named(op) = left_symbol else {
            return None;
        };
        if !matches!(op.as_str(), "<=" | "<" | ">=" | ">") {
            return None;
        }
        let [left_arg0, left_arg1] = left_args.as_slice() else {
            return None;
        };
        let [right_arg0, right_arg1] = right_args.as_slice() else {
            return None;
        };

        let mut differing_args = None;
        for (&left_arg, &right_arg) in left_args.iter().zip(right_args.iter()) {
            if left_arg == right_arg {
                continue;
            }
            if differing_args.replace((left_arg, right_arg)).is_some() {
                return None;
            }
        }
        let (differing_left, differing_right) = differing_args?;

        let premise_literal = {
            let clauses = self.proof_clauses.borrow();
            let premise_clause = clauses.get(premise)?;
            let [premise_literal] = premise_clause.as_slice() else {
                return None;
            };
            *premise_literal
        };
        let TermData::App(Symbol::Named(premise_op), premise_args) =
            self.terms.get(premise_literal)
        else {
            return None;
        };
        if premise_op != "=" {
            return None;
        }
        let [premise_left, premise_right] = premise_args.as_slice() else {
            return None;
        };
        if !((*premise_left == differing_left && *premise_right == differing_right)
            || (*premise_left == differing_right && *premise_right == differing_left))
        {
            return None;
        }

        let op = Self::format_symbol(left_symbol);
        let canonical_left = format!(
            "({op} {} {})",
            self.format_term(*left_arg0),
            self.format_term(*left_arg1)
        );
        let canonical_right = format!(
            "({op} {} {})",
            self.format_term(*right_arg0),
            self.format_term(*right_arg1)
        );
        let printed_left = overrides.get(left)?.clone();
        if surface_order_reversal(&printed_left).as_deref() != Some(canonical_left.as_str()) {
            return None;
        }
        let printed_right = self.format_term(*right);
        if printed_right != canonical_right {
            return None;
        }

        let final_equality = format!("(= {printed_left} {printed_right})");
        if self.format_term(*conclusion) != final_equality {
            return None;
        }
        // `comp_simplify` reverses a non-strict comparison in one step, but a
        // strict one only through `(not (<= ..))`; the shared helper emits
        // whichever the operator needs.
        let mut steps = Vec::new();
        if !authored_assume::comparison_reversal_step(
            &format!("{id}.norm"),
            &printed_left,
            &canonical_left,
            authored_assume::EquivalenceDirection::SurfaceToCanonical,
            &mut steps,
        ) {
            return None;
        }
        // Congruence is checked over the PRINTED premise too: one already
        // spelled as the differing argument pair is cited as is, and one whose
        // rendering commutes a multiplication is repaired with the checked
        // steps the multiplication bridge uses (see `surface_congruence::order`).
        steps.extend(self.canonical_order_cong_steps(
            &format!("{id}.cong"),
            *left,
            *right,
            [&canonical_left, &canonical_right],
            premises,
        )?);
        steps.push(format!(
            "(step {id} (cl {final_equality}) :rule trans :premises ({id}.norm {id}.cong))"
        ));
        Some(steps.join("\n"))
    }

    /// Repair the exact `eq_congruent` surface mismatch produced when an
    /// authored multiplication keeps source operand order in one application
    /// while canonical interning uses the commuted order everywhere else.
    ///
    /// The ordinary internal hypothesis is reflexive, e.g.
    /// `¬((* c 16) = (* c 16))`, but the printed conclusion needs
    /// `(* 16 c) = (* c 16)`. Prove that one AC equality with `aci_simp`, use
    /// it in a corrected `eq_congruent`, weaken it with the original reflexive
    /// hypothesis, then resolve back to the exact original printed clause.
    ///
    /// Any other printed argument/hypothesis mismatch fails closed.
    /// `eq_congruent` over an INDEXED application, re-derived as a subproof.
    ///
    /// WHY. carcara 1.1.0's `eq_congruent` destructures both sides of its
    /// conclusion and accepts only `Term::App` and `Term::Op`. An indexed
    /// application such as `((_ extract 767 384) x104)` is neither, so the step
    /// is REFUSED — not held as a hole, refused, which voids the whole
    /// document:
    ///
    /// ```text
    /// [ERROR] checking failed on step 't44' with rule 'eq_congruent':
    /// term is not an application or operation: '((_ extract 767 384) x104)'
    /// ```
    ///
    /// MEASURED on pinned carcara 1.1.0 with three four-line hand proofs over
    /// the same shape: the clause over an uninterpreted `g` is `valid`; the
    /// clause over `(_ extract 1 0)` under `eq_congruent` is `invalid` with
    /// exactly the error above; and the SAME congruence under the
    /// premise-carrying `cong` rule is `valid`. So this is a checker COVERAGE
    /// limit rather than a false claim by AY — the step really is a congruence
    /// instance — but a refused step is worth exactly as little to an external
    /// reader as a wrong one, so the document must not carry it.
    ///
    /// THE REPAIR IS A DERIVATION, NOT A RELABEL. `cong` proves the equality
    /// from its argument equalities as PREMISES; the traced clause carries
    /// those equalities as NEGATED literals instead. Converting between the two
    /// is `subproof`, a real Alethe rule:
    ///
    /// ```text
    /// (anchor :step tK)
    /// (assume tK.h0 (= a0 b0)) ...              ; one per argument position
    /// (step tK.c (cl (= (f a..) (f b..))) :rule cong :premises (tK.h0 ..))
    /// (step tK.s (cl (= (f b..) (f a..))) :rule symm :premises (tK.c)) ; if flipped
    /// (step tK  (cl (not (= a0 b0)) .. CONCL) :rule subproof :discharge (tK.h0 ..))
    /// ```
    ///
    /// The closing step keeps the ORIGINAL id and the byte-identical traced
    /// clause, so every downstream premise reference is untouched.
    ///
    /// EVERY CHECK IS ON THE PRINTED TEXT, which is the point: the defect class
    /// this file keeps meeting is a rule name taken from the term DAG against
    /// text taken from a surface override. The head symbols, the argument
    /// spellings and the hypothesis orientations are all compared as the
    /// strings that will actually ship. Anything that does not line up exactly
    /// declines and the ordinary rendering runs.
    ///
    /// Deliberately narrow: it fires ONLY when the printed head is an indexed
    /// identifier, which is exactly the shape measured to be refused. An
    /// ordinary application still renders `eq_congruent` byte-identically.
    fn format_indexed_eq_congruent(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<String> {
        if !premises.is_empty() || !args.is_empty() || clause.len() < 2 {
            return None;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        self.charge(printed.iter().map(|p| p.len() as u64).sum());
        if self.work_budget_exhausted() {
            return None;
        }
        let (conclusion, hypotheses) = printed.split_last()?;

        // The conclusion must PRINT as a binary equality between two indexed
        // applications sharing one head.
        let equality = split_application(conclusion, "=")?;
        let [left, right] = equality.as_slice() else {
            return None;
        };
        let (left_head, left_args) = split_printed_indexed_application(left)?;
        let (right_head, right_args) = split_printed_indexed_application(right)?;
        if left_head != right_head
            || left_args.len() != right_args.len()
            || left_args.len() != hypotheses.len()
            || left_args.is_empty()
        {
            return None;
        }

        // Each hypothesis must PRINT as `(not (= a b))`.
        let mut pairs: Vec<(String, String)> = Vec::with_capacity(hypotheses.len());
        for hypothesis in hypotheses {
            let negation = split_application(hypothesis, "not")?;
            let [inner] = negation.as_slice() else {
                return None;
            };
            let equality = split_application(inner, "=")?;
            let [a, b] = equality.as_slice() else {
                return None;
            };
            pairs.push((a.clone(), b.clone()));
        }

        // `cong` reads its premises positionally: premise i must equate the
        // i-th argument of the left application with the i-th of the right.
        // The traced conclusion may carry either orientation; nothing else is
        // accepted, because nothing else IS this congruence.
        let direct = pairs
            .iter()
            .zip(left_args.iter().zip(right_args.iter()))
            .all(|((a, b), (l, r))| a == l && b == r);
        let flipped = pairs
            .iter()
            .zip(left_args.iter().zip(right_args.iter()))
            .all(|((a, b), (l, r))| a == r && b == l);
        if !direct && !flipped {
            return None;
        }

        let cong_conclusion = if direct {
            conclusion.clone()
        } else {
            format!("(= {right} {left})")
        };
        let mut out = format!("(anchor :step {id})\n");
        let mut discharge: Vec<String> = Vec::with_capacity(pairs.len());
        for (index, (a, b)) in pairs.iter().enumerate() {
            let hypothesis_id = format!("{id}.h{index}");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!("(assume {hypothesis_id} (= {a} {b}))\n"),
            );
            discharge.push(hypothesis_id);
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id}.c (cl {cong_conclusion}) :rule cong :premises ({}))\n",
                discharge.join(" ")
            ),
        );
        if !direct {
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!("(step {id}.s (cl {conclusion}) :rule symm :premises ({id}.c))\n"),
            );
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} {} :rule subproof :discharge ({}))",
                self.format_clause(clause),
                discharge.join(" ")
            ),
        );
        Some(out)
    }

    /// The ONE hypothesis of a surface-mutated `eq_congruent` whose printed
    /// equality does not state the printed argument pair at its own index, or
    /// `None` when every hypothesis does (so there is nothing to repair).
    ///
    /// Both lists this reads are PRINTED: hypothesis `k` is judged against
    /// printed argument `k` of each side. More than one mismatch is refused
    /// outright — the repair below rebuilds exactly one literal, so a second
    /// one would ship a clause no premise justifies.
    fn surface_eq_congruent_hypothesis_mismatch(
        &self,
        hypotheses: &[TermId],
        left_args: &[String],
        right_args: &[String],
    ) -> Result<Option<(usize, String, String, String)>, String> {
        let mut mismatch: Option<(usize, String, String, String)> = None;
        for (index, hypothesis) in hypotheses.iter().enumerate() {
            let printed_hypothesis = self.format_term(*hypothesis);
            let Some(not_args) = split_application(&printed_hypothesis, "not") else {
                return Err("eq_congruent hypothesis is not a printed negation".to_string());
            };
            let [negated_equality] = not_args.as_slice() else {
                return Err("eq_congruent hypothesis has malformed negation arity".to_string());
            };
            let Some(equality) = split_application(negated_equality, "=") else {
                return Err("eq_congruent hypothesis does not negate an equality".to_string());
            };
            let [hyp_left, hyp_right] = equality.as_slice() else {
                return Err("eq_congruent hypothesis has malformed equality arity".to_string());
            };
            let expected_left = &left_args[index];
            let expected_right = &right_args[index];
            if (surface_literal::equal_modulo_bitvec_literal_spelling(hyp_left, expected_left)
                && surface_literal::equal_modulo_bitvec_literal_spelling(hyp_right, expected_right))
                || (surface_literal::equal_modulo_bitvec_literal_spelling(hyp_left, expected_right)
                    && surface_literal::equal_modulo_bitvec_literal_spelling(
                        hyp_right,
                        expected_left,
                    ))
            {
                continue;
            }
            if mismatch.is_some() {
                return Err(
                    "more than one surface eq_congruent hypothesis mismatches its arguments"
                        .to_string(),
                );
            }
            mismatch = Some((
                index,
                printed_hypothesis,
                hyp_left.clone(),
                hyp_right.clone(),
            ));
        }
        Ok(mismatch)
    }

    fn surface_eq_congruent_bridge(
        &self,
        id: ProofId,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<Option<String>, String> {
        if self.term_overrides.is_none() {
            return Ok(None);
        }
        if clause.len() < 2 {
            return Ok(None);
        }
        let Some((&conclusion, hypotheses)) = clause.split_last() else {
            return Ok(None);
        };
        let TermData::App(Symbol::Named(eq), equality_args) = self.terms.get(conclusion) else {
            return Ok(None);
        };
        if eq != "=" {
            return Ok(None);
        }
        let [left, right] = equality_args.as_slice() else {
            return Ok(None);
        };
        let TermData::App(left_symbol, left_internal_args) = self.terms.get(*left) else {
            return Ok(None);
        };
        let TermData::App(right_symbol, right_internal_args) = self.terms.get(*right) else {
            return Ok(None);
        };
        if left_symbol != right_symbol || left_internal_args.len() != right_internal_args.len() {
            return Ok(None);
        }

        let operator = Self::format_symbol(left_symbol);
        let printed_left = self.format_term(*left);
        let printed_right = self.format_term(*right);
        let Some(left_args) = split_application(&printed_left, &operator) else {
            return Err(format!(
                "surface left application no longer uses the certified operator {operator} \
                 (printed={:?})",
                surface_congruence::bounded_surface_diagnostic(&printed_left)
            ));
        };
        let Some(right_args) = split_application(&printed_right, &operator) else {
            return Err(format!(
                "surface right application no longer uses the certified operator {operator} \
                 (printed={:?})",
                surface_congruence::bounded_surface_diagnostic(&printed_right)
            ));
        };
        if left_args.len() != right_args.len() || hypotheses.len() != left_args.len() {
            return Err(
                "surface eq_congruent arity no longer matches its equality hypotheses".to_string(),
            );
        }
        if !premises.is_empty() || !args.is_empty() {
            return Err(
                "surface-mutated eq_congruent carries unsupported premises or arguments"
                    .to_string(),
            );
        }

        // #printed-operand-order. `left_args` is read off the PRINTED
        // application and `left_internal_args` off the term DAG, and the
        // Int/Real gate below reads the INTERNAL argument at the printed
        // mismatch index. A whole-application surface override supplies the
        // AUTHOR's spelling, and for an operator whose internal form is
        // order-normalized that need not be the stored order — so the gate
        // could be read off a different argument than the one the emitted
        // step names. Realign each internal list to its printed one, and only
        // ever by an EXACT assignment (every printed argument matched to a
        // distinct internal argument that renders as it); with the stored
        // order already in printed order, or with no such assignment, the
        // stored list is kept and this is byte-identical to what it was.
        let left_internal_args = self
            .internal_args_in_printed_order(&left_args, left_internal_args)
            .unwrap_or_else(|| left_internal_args.clone());
        let right_internal_args = self
            .internal_args_in_printed_order(&right_args, right_internal_args)
            .unwrap_or_else(|| right_internal_args.clone());

        let mut printed_clause: Vec<String> =
            clause.iter().map(|&term| self.format_term(term)).collect();
        let Some((index, original_hypothesis, hyp_left, hyp_right)) =
            self.surface_eq_congruent_hypothesis_mismatch(hypotheses, &left_args, &right_args)?
        else {
            return Ok(None);
        };
        if hyp_left != hyp_right {
            let hyp_left = surface_congruence::bounded_surface_diagnostic(&hyp_left);
            let hyp_right = surface_congruence::bounded_surface_diagnostic(&hyp_right);
            let expected_left = surface_congruence::bounded_surface_diagnostic(&left_args[index]);
            let expected_right = surface_congruence::bounded_surface_diagnostic(&right_args[index]);
            return Err(format!(
                "surface eq_congruent mismatch is not the exact reflexive-hypothesis shape; hypothesis=({hyp_left:?}, {hyp_right:?}); expected=({expected_left:?}, {expected_right:?})"
            ));
        }
        if !matches!(
            self.terms.sort(left_internal_args[index]),
            Sort::Int | Sort::Real
        ) || self.terms.sort(left_internal_args[index])
            != self.terms.sort(right_internal_args[index])
        {
            return Err(
                "surface eq_congruent AC bridge is restricted to Int/Real multiplication"
                    .to_string(),
            );
        }

        let expected_left = &left_args[index];
        let expected_right = &right_args[index];
        let Some(left_mul) = split_application(expected_left, "*") else {
            return Err(
                "surface eq_congruent mismatch is not a multiplication operand swap".to_string(),
            );
        };
        let Some(right_mul) = split_application(expected_right, "*") else {
            return Err(
                "surface eq_congruent mismatch is not a multiplication operand swap".to_string(),
            );
        };
        let ([left_a, left_b], [right_a, right_b]) = (left_mul.as_slice(), right_mul.as_slice())
        else {
            return Err(
                "surface eq_congruent AC bridge requires binary multiplication".to_string(),
            );
        };
        if left_a != right_b
            || left_b != right_a
            || (hyp_left.as_str() != expected_left.as_str()
                && hyp_left.as_str() != expected_right.as_str())
        {
            return Err(
                "surface eq_congruent mismatch is not the exact commuted reflexive premise"
                    .to_string(),
            );
        }

        let Some(ac_step) =
            aci_simp_step::ac_identity_step(format!("{id}.ac"), expected_left, expected_right)
        else {
            return Err("surface eq_congruent AC bridge is not an AC identity".to_string());
        };
        let ac_equality = format!("(= {expected_left} {expected_right})");
        printed_clause[index] = format!("(not {ac_equality})");
        let corrected_clause = format!("(cl {})", printed_clause.join(" "));
        let original_clause = self.format_clause(clause);
        Ok(Some(format!(
            "{ac_step}\n\
             (step {id}.eqc {corrected_clause} :rule eq_congruent)\n\
             (step {id}.acw (cl {ac_equality} {original_hypothesis}) :rule weakening :premises ({id}.ac))\n\
             (step {id} {original_clause} :rule resolution :premises ({id}.eqc {id}.acw))"
        )))
    }

    /// Detect an or_pos/or_neg tautology whose source or-term carries a
    /// surface-syntax override of the form `(=> A B)` and rebuild the step
    /// as the corresponding spec-correct implies_* tautology (see the call
    /// site in `format_generic_step`). Returns `None` — leaving the step
    /// untouched — unless every literal can be matched exactly, so this is
    /// purely a printing-shape correction, never a semantic change.
    fn resugar_implies_tautology(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
        use ay_core::AletheRule as R;
        if !matches!(rule, R::OrPos(_) | R::OrNeg) || args.len() != 1 {
            return None;
        }
        let source = args[0];
        // `source` may be a quantified-body instance whose authored spelling
        // lives in the proof-local Skolem override table, not the global
        // assertion override table.
        let override_str = self.format_term(source);
        let (a_str, b_str) = split_binary_implies(&override_str)?;
        let TermData::App(sym, disjuncts) = self.terms.get(source) else {
            return None;
        };
        if sym.name() != "or" {
            return None;
        }
        match rule {
            R::OrPos(_) => {
                if disjuncts.len() != 2 {
                    return None;
                }
                // Identify the antecedent disjunct `(not A)` and consequent
                // `B` by exact surface matching. A flattened conjunction
                // antecedent needs a longer derivation and falls through to
                // the generic surface-tautology bridge.
                let mut found: Option<(TermId, TermId)> = None; // (not_a, b)
                for (i, &disjunct) in disjuncts.iter().enumerate() {
                    if let TermData::Not(inner) = self.terms.get(disjunct) {
                        if self.format_term(*inner) == a_str
                            && self.format_term(disjuncts[1 - i]) == b_str
                        {
                            found = Some((disjunct, disjuncts[1 - i]));
                            break;
                        }
                    }
                }
                let (not_a, b_term) = found?;
                // Clause must be exactly {¬source, (not A), B}.
                if clause.len() != 3 {
                    return None;
                }
                let mut rest: Vec<TermId> = Vec::with_capacity(2);
                let mut saw_not_source = false;
                for &l in clause {
                    if !saw_not_source
                        && matches!(self.terms.get(l), TermData::Not(inner) if *inner == source)
                    {
                        saw_not_source = true;
                    } else {
                        rest.push(l);
                    }
                }
                if !saw_not_source {
                    return None;
                }
                rest.sort_unstable();
                let mut expected = [not_a, b_term];
                expected.sort_unstable();
                if rest != expected {
                    return None;
                }
                Some(format!(
                    "(step {id} (cl (not {override_str}) {} {}) :rule implies_pos)",
                    self.format_term(not_a),
                    self.format_term(b_term)
                ))
            }
            R::OrNeg => {
                if clause.len() != 2 || !clause.contains(&source) {
                    return None;
                }
                let other = clause.iter().copied().find(|&l| l != source)?;
                let other_str = self.format_term(other);
                if other_str == format!("(not {b_str})") {
                    return Some(format!(
                        "(step {id} (cl {override_str} {other_str}) :rule implies_neg2)"
                    ));
                }

                if other_str == a_str {
                    return Some(format!(
                        "(step {id} (cl {override_str} {other_str}) :rule implies_neg1)"
                    ));
                }

                let conjuncts = split_application(&a_str, "and")?;
                let position = conjuncts.iter().position(|part| part == &other_str)?;
                Some(format!(
                    "(step {id}.imp (cl {override_str} {a_str}) :rule implies_neg1)\n\
                     (step {id}.and (cl (not {a_str}) {other_str}) :rule and_pos :args ({position}))\n\
                     (step {id} (cl {override_str} {other_str}) :rule resolution :premises ({id}.imp {id}.and))"
                ))
            }
            _ => None,
        }
    }

    /// Resugar a premiseless `and_pos` extraction over an arithmetic
    /// equality's and-split (see the call site in `format_generic_step`)
    /// into a `la_generic` orientation lemma. The internal step is a valid
    /// `and_pos` over the genuine and-term `(and (<= ..) (<= ..))`, but the
    /// term PRINTS as its surface equality `(= L R)` — a shape no external
    /// checker accepts as `and_pos`. The printed clause
    /// `(cl (not (= L R)) (<= A B))` is exactly the Alethe `la_generic`
    /// tautology with coefficients `(s 1)`: negating the clause asserts the
    /// equality together with the strict complement of the bound, and the
    /// signed unit combination `s·(L − R) + (A − B) > 0` (resp. `B − A`)
    /// collapses to `0 > 0`. The sign `s` is chosen by exact printed-operand
    /// match, so the emitted step is checkable as printed (validated against
    /// carcara). Fail-open: any shape mismatch keeps the default `and_pos`
    /// rendering byte-identical.
    fn resugar_equality_split_and_pos(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
    ) -> Option<String> {
        if !matches!(rule, ay_core::AletheRule::AndPos(_)) || clause.len() != 2 {
            return None;
        }
        // Identify the gate literal `(not T)` with T a genuine binary
        // and-term, and the extracted conjunct literal (an operand of T).
        let (gate_idx, source) = clause.iter().enumerate().find_map(|(i, &l)| {
            if let TermData::Not(inner) = self.terms.get(l) {
                if matches!(
                    self.terms.get(*inner),
                    TermData::App(sym, conjs) if sym.name() == "and" && conjs.len() == 2
                ) {
                    return Some((i, *inner));
                }
            }
            None
        })?;
        let conjunct = clause[1 - gate_idx];
        let TermData::App(_, conjs) = self.terms.get(source) else {
            return None;
        };
        if !conjs.contains(&conjunct) {
            return None;
        }
        // The and-term must PRINT as a binary equality (its surface
        // override); a term printed as `(and ...)` is externally-valid
        // and_pos and keeps the default rendering.
        let source_str = self.format_term(source);
        let eq_ops = split_application(&source_str, "=")?;
        let [eq_lhs, eq_rhs] = eq_ops.as_slice() else {
            return None;
        };
        // The extracted conjunct must print as a NON-strict bound over the
        // same printed operands (a strict bound cannot form this tautology:
        // its negation is non-strict and the unit combination is `0 >= 0`).
        let conjunct_str = self.format_term(conjunct);
        let (bound_ops, negation_is_lhs_minus_rhs) = match split_application(&conjunct_str, "<=") {
            // ¬(<= A B) ⇒ A − B > 0
            Some(ops) => (ops, true),
            // ¬(>= A B) ⇒ B − A > 0
            None => (split_application(&conjunct_str, ">=")?, false),
        };
        let [bound_a, bound_b] = bound_ops.as_slice() else {
            return None;
        };
        // Choose the equality coefficient s so that s·(L − R) cancels the
        // bound negation's positive difference exactly.
        let (pos_diff_lhs, pos_diff_rhs) = if negation_is_lhs_minus_rhs {
            (bound_a, bound_b) // A − B > 0
        } else {
            (bound_b, bound_a) // B − A > 0
        };
        let sign = if eq_lhs == pos_diff_rhs && eq_rhs == pos_diff_lhs {
            "1" // s·(L − R) = R' − L' cancellation with s = +1
        } else if eq_lhs == pos_diff_lhs && eq_rhs == pos_diff_rhs {
            "(- 1)"
        } else {
            return None;
        };
        let (first_lit, second_lit, args_str) = if gate_idx == 0 {
            (
                format!("(not {source_str})"),
                conjunct_str,
                format!("{sign} 1"),
            )
        } else {
            (
                conjunct_str,
                format!("(not {source_str})"),
                format!("1 {sign}"),
            )
        };
        Some(format!(
            "(step {id} (cl {first_lit} {second_lit}) :rule la_generic :args ({args_str}))"
        ))
    }

    /// Resugar an `or` decomposition step (see the call site in
    /// `format_generic_step`) whose premise assume prints as
    /// `(not (and A1 .. An))` into the spec-correct `not_and` step. Purely a
    /// printing-shape correction, taken only when every printed clause
    /// literal matches `(not Ai)` in surface-operand order; `None` keeps the
    /// default rendering byte-identical.
    fn resugar_not_and_decomposition(
        &self,
        id: ProofId,
        clause: &[TermId],
        premise: ProofId,
    ) -> Option<String> {
        let source = *self.assume_terms.borrow().get(&premise)?;
        // The internal premise term must be a genuine or-term (the
        // decomposition the `or` rule certified internally).
        let TermData::App(sym, disjuncts) = self.terms.get(source) else {
            return None;
        };
        if sym.name() != "or" || disjuncts.len() != clause.len() {
            return None;
        }
        let source_str = self.format_term(source);
        let conjuncts = split_not_and(&source_str)?;
        if conjuncts.len() != clause.len() {
            return None;
        }
        let mut lits: Vec<String> = Vec::with_capacity(clause.len());
        for (&lit, conjunct) in clause.iter().zip(conjuncts.iter()) {
            let printed = self.format_term(lit);
            if printed != format!("(not {conjunct})") {
                return None;
            }
            lits.push(printed);
        }
        Some(format!(
            "(step {id} (cl {}) :rule not_and :premises ({premise}))",
            lits.join(" ")
        ))
    }

    /// Reorder an `or` step's conclusion literals into the order the premise's
    /// printed or-term lists its disjuncts, or `None` to leave the step exactly
    /// as it is.
    ///
    /// carcara checks `or` POSITIONALLY: given premise `(or D1 .. Dn)` the
    /// conclusion must be `(cl D1 .. Dn)` in that order. AY's internal clause
    /// is a set, so it is a permutation of the disjuncts in general and the
    /// step is rejected with "expected terms to be equal: 'Di' and 'Dj'".
    ///
    /// Matching is done on the PRINTED strings, which is exactly what carcara
    /// parses: a surface override can make two distinct internal terms render
    /// identically, and in the emitted document those are interchangeable. It
    /// is also what makes the check total — no internal-vs-surface skew can
    /// make this produce a clause the checker reads differently.
    ///
    /// Fail-closed in the conservative direction: any shape this cannot prove
    /// is a pure permutation (premise not a printed or-term, arity mismatch,
    /// a literal with no partner) returns `None` and the caller renders the
    /// step byte-unchanged. Returns `None` for an already-ordered clause too,
    /// so only genuinely permuted steps differ from today's output.
    ///
    /// Only the RENDERING moves. Nothing downstream indexes a premise clause
    /// positionally — all five `proof_clauses` consumers were checked — and
    /// the recorded clause for this step is unchanged, so a later step that
    /// takes this one as a premise sees exactly what it saw before.
    fn or_conclusion_in_premise_order(
        &self,
        clause: &[TermId],
        premise: ProofId,
    ) -> Option<Vec<TermId>> {
        let source = {
            let clauses = self.proof_clauses.borrow();
            let [literal] = clauses.get(&premise)?.as_slice() else {
                return None;
            };
            *literal
        };
        let disjuncts = split_application(&self.format_term(source), "or")?;
        if disjuncts.len() != clause.len() {
            return None;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        // Greedy multiset match; `used` keeps repeated disjuncts honest by
        // consuming a distinct clause position for each occurrence.
        let mut used = vec![false; clause.len()];
        let mut reordered: Vec<TermId> = Vec::with_capacity(clause.len());
        for disjunct in &disjuncts {
            let position = printed
                .iter()
                .enumerate()
                .position(|(index, lit)| !used[index] && lit == disjunct)?;
            used[position] = true;
            reordered.push(clause[position]);
        }
        if reordered == clause {
            return None;
        }
        Some(reordered)
    }

    /// Reconcile an `or` decomposition whose printed conclusion states an
    /// arithmetic order atom in the OPPOSITE orientation to the one its own
    /// premise printed.
    ///
    /// `or` compares premise disjuncts against conclusion literals TEXTUALLY,
    /// so a document holding an authored `assume` beside a canonicalized
    /// derivation is refused — "expected terms to be equal: '(<= 10 a)' and
    /// '(>= a 10)'" — even though AY derived the step. That is the same defect
    /// the premise-free tautology family has, on the other side of the premise
    /// line, and it takes the same repair: see
    /// [`order_orientation_bridge_clause`] for why stating the orientation is
    /// the only faithful option and why `la_generic` is what states it.
    ///
    /// Emits the decomposition over the PREMISE's own orientation and order (a
    /// spec instance of `or` by construction — its literals are literally the
    /// premise's printed disjuncts), one orientation lemma per flipped literal,
    /// and a resolution concluding the traced clause under this step's own id,
    /// so downstream premise references are untouched.
    ///
    /// Nothing is relabelled: the step still claims `or`, over the operands
    /// `or` actually relates, and every literal it gains is separately checked.
    /// Fail-closed on anything else — a premise that is not a printed or-term,
    /// an arity mismatch, or a literal whose partner differs by more than its
    /// order orientation. Returns `None` when no literal is flipped, leaving
    /// [`Self::or_conclusion_in_premise_order`] to render the step as it does
    /// today.
    fn reorient_or_decomposition(
        &self,
        id: ProofId,
        clause: &[TermId],
        premise: ProofId,
    ) -> Option<String> {
        let source = {
            let clauses = self.proof_clauses.borrow();
            let [literal] = clauses.get(&premise)?.as_slice() else {
                return None;
            };
            *literal
        };
        let disjuncts = split_application(&self.format_term(source), "or")?;
        if disjuncts.len() != clause.len() {
            return None;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        // Greedy multiset match, exact partners first: a repeated literal must
        // consume a distinct position, and a literal that IS present must never
        // be spent on an orientation bridge it does not need.
        let mut used = vec![false; clause.len()];
        let mut traced: Vec<String> = Vec::with_capacity(clause.len());
        let mut bridges: Vec<String> = Vec::new();
        for disjunct in &disjuncts {
            if let Some(position) = printed
                .iter()
                .enumerate()
                .position(|(index, lit)| !used[index] && lit == disjunct)
            {
                used[position] = true;
                traced.push(printed[position].clone());
                continue;
            }
            let (position, bridge_clause) =
                printed.iter().enumerate().find_map(|(index, lit)| {
                    if used[index] {
                        return None;
                    }
                    Some((index, order_orientation_bridge_clause(disjunct, lit)?))
                })?;
            used[position] = true;
            traced.push(printed[position].clone());
            bridges.push(bridge_clause);
        }
        if bridges.is_empty() {
            return None;
        }
        let mut out = format!(
            "(step {id}.o (cl {}) :rule or :premises ({premise}))\n",
            disjuncts.join(" ")
        );
        let mut premise_ids = format!("{id}.o");
        for (index, bridge_clause) in bridges.iter().enumerate() {
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id}.b{index} (cl {bridge_clause}) :rule la_generic :args (1 1))\n"
                ),
            );
            let _ = std::fmt::Write::write_fmt(&mut premise_ids, format_args!(" {id}.b{index}"));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl {}) :rule resolution :premises ({premise_ids}))",
                traced.join(" ")
            ),
        );
        Some(out)
    }

    fn format_anchor(end_step: ProofId, variables: &[(String, Sort)]) -> String {
        let mut result = format!("(anchor :step {end_step}");
        if !variables.is_empty() {
            let vars_str: Vec<String> = variables
                .iter()
                .map(|(name, sort)| {
                    format!("({} {})", quote_symbol(name), format_sort_alethe(sort))
                })
                .collect();
            let _ = std::fmt::Write::write_fmt(
                &mut result,
                format_args!(" :args ({})", vars_str.join(" ")),
            );
        }
        result.push(')');
        result
    }

    /// Format a clause (list of literals) as "(cl lit1 lit2 ...)"
    fn format_clause(&self, clause: &[TermId]) -> String {
        if clause.is_empty() {
            "(cl)".to_string()
        } else {
            // Append literals directly into one buffer (#proof-tax): the
            // legacy `map(format_term).collect::<Vec<String>>() + join`
            // cloned every (cached) literal rendering into a fresh String
            // per occurrence — the dominant allocation churn of Alethe
            // emission on resolution-heavy proofs. Output is byte-identical.
            let mut out = String::from("(cl");
            for &lit in clause {
                out.push(' ');
                self.write_derived_literal_into(&mut out, lit);
            }
            out.push(')');
            out
        }
    }

    /// Format term data recursively
    fn format_term_data(&self, term: &TermData) -> String {
        match term {
            TermData::Var(name, _) => quote_symbol(name),

            TermData::Const(c) => Self::format_constant(c),

            TermData::Not(inner) => {
                format!("(not {})", self.format_term(*inner))
            }

            TermData::Ite(cond, then_br, else_br) => {
                format!(
                    "(ite {} {} {})",
                    self.format_term(*cond),
                    self.format_term(*then_br),
                    self.format_term(*else_br)
                )
            }

            TermData::App(sym, args) => {
                // DATATYPE TESTERS (#dt-tester-printing): AY's internal spelling
                // is the plain symbol `is-C` (see the `strip_prefix("is-")`
                // consumers in executor/mbqi.rs, model/dt_construct.rs and
                // ay-model-check/dt_axiom.rs). SMT-LIB has no such function —
                // a tester is the INDEXED identifier `(_ is C)`, so printing
                // `(is-C t)` makes every consumer reject the file with
                // "identifier 'is-C' is not defined". Measured: a blocksworld
                // proof carried 389 such occurrences and carcara returned
                // `invalid` — strictly worse than a hole, since no rule can
                // even run on an unparseable file.
                let mut out = String::new();
                self.write_application_into(&mut out, sym, args);
                out
            }

            TermData::Let(bindings, body) => {
                let bindings_str: Vec<String> = bindings
                    .iter()
                    .map(|(name, term)| {
                        format!("({} {})", quote_symbol(name), self.format_term(*term))
                    })
                    .collect();
                format!(
                    "(let ({}) {})",
                    bindings_str.join(" "),
                    self.format_term(*body)
                )
            }

            TermData::Forall(vars, body, _) => self.format_quantifier("forall", vars, *body),

            TermData::Exists(vars, body, _) => self.format_quantifier("exists", vars, *body),
            _ => unreachable!("unexpected TermData variant"),
        }
    }

    /// Format a quantifier (forall/exists) with sorted variable list.
    fn format_quantifier(&self, keyword: &str, vars: &[(String, Sort)], body: TermId) -> String {
        let vars_str: Vec<String> = vars
            .iter()
            .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_sort_alethe(sort)))
            .collect();
        format!(
            "({} ({}) {})",
            keyword,
            vars_str.join(" "),
            self.format_term(body)
        )
    }

    /// Format a constant value
    fn format_constant(c: &Constant) -> String {
        match c {
            Constant::Bool(true) => "true".to_string(),
            Constant::Bool(false) => "false".to_string(),
            Constant::Int(i) => {
                if i.sign() == Sign::Minus {
                    format!("(- {})", i.magnitude())
                } else {
                    i.to_string()
                }
            }
            Constant::Rational(r) => {
                let rat = &r.0;
                if rat.is_integer() {
                    if rat.numer().sign() == Sign::Minus {
                        format!("(- {}.0)", rat.numer().magnitude())
                    } else {
                        format!("{}.0", rat.numer())
                    }
                } else if rat.numer().sign() == Sign::Minus {
                    format!("(- (/ {}.0 {}.0))", rat.numer().magnitude(), rat.denom())
                } else {
                    format!("(/ {}.0 {}.0)", rat.numer(), rat.denom())
                }
            }
            Constant::BitVec { value, width } => {
                // Use binary format for bitvectors
                format!("#b{:0>width$b}", value, width = *width as usize)
            }
            Constant::String(s) => string_literal(s),
            Constant::FiniteField { value, field } => {
                format!("(as ff{value} (_ FiniteField {}))", field.modulus())
            }
            _ => unreachable!("unexpected Constant variant"),
        }
    }

    /// Format a function symbol
    fn format_symbol(sym: &Symbol) -> String {
        match sym {
            Symbol::Named(name) => quote_symbol(name),
            Symbol::Indexed(name, indices) => {
                let indices_str: Vec<String> = indices.iter().map(ToString::to_string).collect();
                format!("(_ {} {})", quote_symbol(name), indices_str.join(" "))
            }
            _ => unreachable!("unexpected Symbol variant"),
        }
    }

    fn format_external_args(
        &self,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<Vec<String>> {
        // Clausification proof annotations carry the source Boolean term as an
        // internal bookkeeping arg, but Alethe expects rule-specific numeric
        // positions (for `and_pos` / `or_neg`) or no args at all.
        if premises.is_empty() {
            match rule {
                ay_core::AletheRule::AndPos(position) => {
                    return Some(vec![position.to_string()]);
                }
                ay_core::AletheRule::OrNeg => {
                    if let Some(position) = self.infer_or_neg_position(clause, args) {
                        return Some(vec![position.to_string()]);
                    }
                }
                _ => {}
            }

            if self.uses_internal_source_term_arg(rule, clause, args) {
                return None;
            }
        }

        if args.is_empty() {
            None
        } else {
            Some(args.iter().map(|a| self.format_term(*a)).collect())
        }
    }

    fn uses_internal_source_term_arg(
        &self,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> bool {
        if args.len() != 1
            || !matches!(
                rule,
                ay_core::AletheRule::AndPos(_)
                    | ay_core::AletheRule::AndNeg
                    | ay_core::AletheRule::True
                    | ay_core::AletheRule::False
                    | ay_core::AletheRule::OrPos(_)
                    | ay_core::AletheRule::OrNeg
                    | ay_core::AletheRule::ImpliesPos
                    | ay_core::AletheRule::ImpliesNeg1
                    | ay_core::AletheRule::ImpliesNeg2
                    | ay_core::AletheRule::EquivPos1
                    | ay_core::AletheRule::EquivPos2
                    | ay_core::AletheRule::EquivNeg1
                    | ay_core::AletheRule::EquivNeg2
                    | ay_core::AletheRule::ItePos1
                    | ay_core::AletheRule::ItePos2
                    | ay_core::AletheRule::IteNeg1
                    | ay_core::AletheRule::IteNeg2
                    | ay_core::AletheRule::XorPos1
                    | ay_core::AletheRule::XorPos2
                    | ay_core::AletheRule::XorNeg1
                    | ay_core::AletheRule::XorNeg2
            )
        {
            return false;
        }

        let source_term = args[0];
        clause
            .iter()
            .copied()
            .any(|lit| lit == source_term || self.is_negation_of(lit, source_term))
    }

    fn infer_or_neg_position(&self, clause: &[TermId], args: &[TermId]) -> Option<usize> {
        if clause.len() != 2 {
            return None;
        }

        let source_term = args.first().copied().or_else(|| {
            clause.iter().copied().find(|lit| {
                matches!(
                    self.terms.get(*lit),
                    TermData::App(Symbol::Named(name), _) if name == "or"
                )
            })
        })?;

        let disjuncts = match self.terms.get(source_term) {
            TermData::App(Symbol::Named(name), disjuncts) if name == "or" => disjuncts,
            _ => return None,
        };

        // The non-source clause literal is the NEGATION of disjunct k —
        // either the literal `(not d)` (a raw double negation when d is
        // itself negative) or, when d is `(not inner)`, the
        // double-negation-stripped `inner`.
        let other = clause.iter().copied().find(|&lit| lit != source_term)?;

        let internal = disjuncts
            .iter()
            .position(|&disjunct| match self.terms.get(disjunct) {
                TermData::Not(inner) => {
                    *inner == other
                        || matches!(self.terms.get(other), TermData::Not(oin) if *oin == disjunct)
                }
                _ => matches!(self.terms.get(other), TermData::Not(oin) if *oin == disjunct),
            })?;

        // The position argument refers to the disjunct's position in the
        // PRINTED or-term. When the term carries a surface-syntax override
        // (e.g. the problem file's own argument order before canonical
        // argument sorting), recompute the index against the printed form.
        Some(self.surface_disjunct_position(source_term, disjuncts[internal], internal))
    }

    /// Position of `disjunct` among the printed arguments of the printed
    /// `or`-term `source_term`. Falls back to `internal` when the printed
    /// form is not an `(or ...)` application or the disjunct's rendering is
    /// not found among its arguments (both only possible with exotic
    /// overrides).
    fn surface_disjunct_position(
        &self,
        source_term: TermId,
        disjunct: TermId,
        internal: usize,
    ) -> usize {
        let Some(overrides) = self.term_overrides else {
            return internal;
        };
        if !overrides.contains_key(&source_term) {
            return internal;
        }
        let printed = self.format_term(source_term);
        let Some(surface_args) = split_application(&printed, "or") else {
            return internal;
        };
        let disjunct_str = self.format_term(disjunct);
        surface_args
            .iter()
            .position(|arg| *arg == disjunct_str)
            .unwrap_or(internal)
    }

    /// Re-derive a clausification tautology step from the PRINTED form of
    /// its source term (see the call site in `format_generic_step`).
    ///
    /// The internal proof step was built from the canonical term: operands
    /// in hash-cons order, `(not x)` operands negated by double-negation
    /// STRIPPING. The printed source term follows the problem file's surface
    /// syntax, so strict Alethe requires the step's literals in the printed
    /// operand order, `(not (not x))` for a negated `(not x)` operand, and —
    /// for operand-order-sensitive rule pairs like `xor_neg1`/`xor_neg2` —
    /// possibly the sibling rule variant.
    ///
    /// This searches the rule family's spec templates for the (unique
    /// modulo argument symmetry) instantiation over the printed operands
    /// whose double-negation-stripped literal multiset equals the printed
    /// traced clause, then emits:
    ///   - [`SurfaceTautology::DefaultIsExact`] when the aligned single step is
    ///     already what the default rendering would print (keeping bytes
    ///     identical);
    ///   - a single spec-shaped step when only order/variant/position-arg
    ///     differ; or
    ///   - the spec-shaped step + one `not_not` bridge per stripped literal
    ///     (`(cl (not (not (not x))) x)` per the Alethe spec) + a final
    ///     resolution concluding the EXACT traced clause under this step's
    ///     own id, so downstream premise references stay untouched.
    ///
    /// When NO template over the printed surface reproduces the clause it
    /// answers [`SurfaceTautology::NoMatch`], which is the caller's authority
    /// to fail loud rather than ship a step naming a rule the printed text does
    /// not instantiate.
    ///
    /// This entry point decides WHICH printed source term to judge the step
    /// against; [`Self::format_surface_tautology_over`] does the judging.
    ///
    /// The source used to be read exclusively from the step's proof-only
    /// `args`. That made the whole predicate **silently inert** for every
    /// producer that does not set it: such a step fell through to the default
    /// rendering with no judgement at all, and `Unjudged` reads exactly like
    /// "fine". Three defects of that one shape have shipped — `or_pos` over a
    /// De Morgan surface, an indexed `eq_congruent`, and `equiv_pos2` over an
    /// order atom — and the third was live on a hole-free, trust-free,
    /// self-checkable document the declared external checker refused. Each was
    /// answered with a per-rule guard, and each guard was outrun by the next
    /// shape, because the hole is not in any rule: it is in the channel that
    /// supplies the source.
    ///
    /// Every rule in this family states its source term IN its own clause, at
    /// a polarity and head symbol the rule itself fixes (`equiv_*` conclude
    /// over an `=`, `ite_*` over an `ite`, `and_neg` over an `and`, ...). So
    /// when `args` carries no source, recover the candidates from the PRINTED
    /// clause and judge each one. Silence is then no longer available to a
    /// rule in the family: if no candidate source makes the printed step a
    /// spec instance, the answer is `NoMatch` and the caller declines the
    /// export. Rules outside the family still answer `Unjudged`, which is the
    /// honest verdict for a predicate that has nothing to say about them.
    fn format_surface_tautology(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> SurfaceTautology {
        if let [source] = args {
            let source_str = self.format_term(*source);
            return self.format_surface_tautology_over(id, rule, clause, args, source_str);
        }
        let Some((negated, heads)) = surface_tautology_source_signature(rule) else {
            return SurfaceTautology::Unjudged;
        };
        let mut sources: Vec<String> = Vec::new();
        for &literal in clause {
            let printed = self.format_derived_literal(literal);
            // Recovery reads every clause literal; charge it like every other
            // printed-surface scan so a pathological clause degrades to the
            // honest "no certificate emitted" warning rather than stalling.
            self.charge(printed.len() as u64);
            if self.work_budget_exhausted() {
                return SurfaceTautology::Unjudged;
            }
            let candidate = if negated {
                match split_application(&printed, "not") {
                    Some(inner) if inner.len() == 1 => inner[0].clone(),
                    _ => continue,
                }
            } else {
                printed
            };
            if !printed_head_symbol(&candidate).is_some_and(|head| heads.contains(&head.as_str())) {
                continue;
            }
            if !sources.contains(&candidate) {
                sources.push(candidate);
            }
        }
        if sources.is_empty() {
            // A premise-free step of THIS rule states its source term in its
            // own clause, at this polarity and head symbol. A printed clause
            // holding no such literal cannot be a spec instance of the rule
            // the step names, whatever the term store says about it, so the
            // default rendering below the call site would ship a false claim.
            return SurfaceTautology::NoMatch;
        }
        for source_str in sources {
            match self.format_surface_tautology_over(id, rule, clause, args, source_str) {
                SurfaceTautology::NoMatch => {}
                judged => return judged,
            }
        }
        SurfaceTautology::NoMatch
    }

    /// Judge one premise-free tautologous step against ONE printed source
    /// term. See [`Self::format_surface_tautology`] for how that source is
    /// chosen and what each verdict authorizes.
    fn format_surface_tautology_over(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
        source_str: String,
    ) -> SurfaceTautology {
        use ay_core::AletheRule as R;

        /// One spec literal: the source term (positive or negated) or the
        /// operand at an index (positive or negated).
        #[derive(Clone, Copy)]
        enum Lit {
            Source(bool /* negated */),
            Operand(usize, bool /* negated */),
        }
        enum Bridge {
            /// `not (not x)` in the spec step was compacted to `x` in the
            /// traced proof.
            NotNot { spec_lit: String, inner: String },
            /// Negated arithmetic order was normalized to its reversed dual,
            /// e.g. `not (<= a b)` to `(< b a)`.
            LinearOrder { operand: String, dual: String },
            /// ONE arithmetic order atom printed in the two orientations AY's
            /// order constructors treat as the same atom — spec `(<= 10 a)`
            /// against traced `(>= a 10)`. Carries the already-built clause
            /// from [`order_orientation_bridge_clause`], which is the single
            /// definition of this device.
            OrderOrientation { bridge_clause: String },
        }
        struct Template {
            rule: &'static str,
            lits: &'static [Lit],
        }
        use Lit::{Operand, Source};

        // Re-deriving from the printed source term re-splits `source_str`
        // per template and clones its operand vector per position; on huge
        // printed terms (QF_ALIA pp-family) this is the emission hotspot.
        // Charge the split cost and fall back to the generic rendering once
        // the synthesized-default work budget is exhausted (#A2b) — the
        // caller's per-step check then degrades to the honest
        // "no certificate emitted" warning.
        self.charge(source_str.len() as u64);
        if self.work_budget_exhausted() {
            return SurfaceTautology::Unjudged;
        }
        if let Some(text) = self.format_chainable_equiv_surface(id, rule, clause, &source_str) {
            return SurfaceTautology::Rendered(text);
        }

        // Spec templates per rule family (Alethe spec, "Tautologous rules"),
        // keyed by the printed operator. `or`-family rules also try `=>`:
        // elaboration desugars implications to or-terms, and the printed
        // surface form is the implication.
        let n_ary_positions = |n: usize| 0..n;
        let mut candidates: Vec<(Vec<String>, Template)> = Vec::new();
        let mut push_for_op = |op: &str, templates: Vec<Template>| {
            if let Some(ops) = surface_chain_equiv::fixed_shape_operands(&source_str, op) {
                for t in templates {
                    candidates.push((ops.clone(), t));
                }
            }
        };

        const XOR_POS1: &[Lit] = &[Source(true), Operand(0, false), Operand(1, false)];
        const XOR_POS2: &[Lit] = &[Source(true), Operand(0, true), Operand(1, true)];
        const XOR_NEG1: &[Lit] = &[Source(false), Operand(0, false), Operand(1, true)];
        const XOR_NEG2: &[Lit] = &[Source(false), Operand(0, true), Operand(1, false)];
        const EQUIV_POS1: &[Lit] = &[Source(true), Operand(0, false), Operand(1, true)];
        const EQUIV_POS2: &[Lit] = &[Source(true), Operand(0, true), Operand(1, false)];
        // MEASURED against the pinned checker, not read off the rule names.
        // carcara 1.1.0 accepts `equiv_neg1` for the NEGATED pair and
        // `equiv_neg2` for the positive one; this table had the two the other
        // way round. That is a silent relabel: a clause that IS a correct
        // `equiv_neg1` was renamed to `equiv_neg2`, and the checker refuses it
        // ("expected terms to be equal: 'p' and '(not p)'"). Every other entry
        // in this block was re-measured the same way and is correct.
        const EQUIV_NEG1: &[Lit] = &[Source(false), Operand(0, true), Operand(1, true)];
        const EQUIV_NEG2: &[Lit] = &[Source(false), Operand(0, false), Operand(1, false)];
        const ITE_POS1: &[Lit] = &[Source(true), Operand(0, false), Operand(2, false)];
        const ITE_POS2: &[Lit] = &[Source(true), Operand(0, true), Operand(1, false)];
        const ITE_NEG1: &[Lit] = &[Source(false), Operand(0, false), Operand(2, true)];
        const ITE_NEG2: &[Lit] = &[Source(false), Operand(0, true), Operand(1, true)];
        const IMPLIES_POS: &[Lit] = &[Source(true), Operand(0, true), Operand(1, false)];
        const IMPLIES_NEG1: &[Lit] = &[Source(false), Operand(0, false)];
        const IMPLIES_NEG2: &[Lit] = &[Source(false), Operand(1, true)];

        let template = |rule: &'static str, lits: &'static [Lit]| Template { rule, lits };
        let implies_templates = || {
            vec![
                template("implies_pos", IMPLIES_POS),
                template("implies_neg1", IMPLIES_NEG1),
                template("implies_neg2", IMPLIES_NEG2),
            ]
        };

        // Positional templates need owned literal vectors; collect those
        // separately as (ops, rule, lits, position).
        let mut positional: Vec<(Vec<String>, &'static str, Vec<Lit>, usize)> = Vec::new();
        match rule {
            R::OrPos(_) => {
                if let Some(ops) = split_application(&source_str, "or") {
                    let mut lits = vec![Source(true)];
                    lits.extend(n_ary_positions(ops.len()).map(|i| Operand(i, false)));
                    positional.push((ops, "or_pos", lits, usize::MAX));
                }
                push_for_op("=>", implies_templates());
                // De Morgan surface `(not (and A1 .. An))`: no premise-free
                // Alethe tautology concludes (cl (not ¬(and A..)) (not A1) ..
                // (not An)) directly; derive it honestly from the printed
                // shape (not_simplify + equiv_pos1 + and_neg + resolution).
                if let Some(text) = self.format_not_and_or_pos(id, clause, &source_str) {
                    return SurfaceTautology::Rendered(text);
                }
            }
            R::OrNeg => {
                if let Some(ops) = split_application(&source_str, "or") {
                    // One cloned operand vector per position: quadratic in
                    // the printed operand bytes. Charge upfront (#A2b).
                    let ops_bytes: u64 = ops.iter().map(|o| o.len() as u64).sum();
                    self.charge(ops_bytes.saturating_mul(ops.len() as u64));
                    if self.work_budget_exhausted() {
                        return SurfaceTautology::Unjudged;
                    }
                    for k in n_ary_positions(ops.len()) {
                        positional.push((
                            ops.clone(),
                            "or_neg",
                            vec![Source(false), Operand(k, true)],
                            k,
                        ));
                    }
                }
                push_for_op("=>", implies_templates());
                // De Morgan surface: (cl ¬(and A..) Ak) is spec `and_pos`.
                if let Some(ops) = split_not_and(&source_str) {
                    let ops_bytes: u64 = ops.iter().map(|o| o.len() as u64).sum();
                    self.charge(ops_bytes.saturating_mul(ops.len() as u64));
                    if self.work_budget_exhausted() {
                        return SurfaceTautology::Unjudged;
                    }
                    for k in n_ary_positions(ops.len()) {
                        positional.push((
                            ops.clone(),
                            "and_pos",
                            vec![Source(false), Operand(k, false)],
                            k,
                        ));
                    }
                }
            }
            R::AndNeg => {
                if let Some(ops) = split_application(&source_str, "and") {
                    let mut lits = vec![Source(false)];
                    lits.extend(n_ary_positions(ops.len()).map(|i| Operand(i, true)));
                    positional.push((ops, "and_neg", lits, usize::MAX));
                }
            }
            R::XorPos1 | R::XorPos2 => push_for_op(
                "xor",
                vec![
                    template("xor_pos1", XOR_POS1),
                    template("xor_pos2", XOR_POS2),
                ],
            ),
            R::XorNeg1 | R::XorNeg2 => push_for_op(
                "xor",
                vec![
                    template("xor_neg1", XOR_NEG1),
                    template("xor_neg2", XOR_NEG2),
                ],
            ),
            R::EquivPos1 | R::EquivPos2 => push_for_op(
                "=",
                vec![
                    template("equiv_pos1", EQUIV_POS1),
                    template("equiv_pos2", EQUIV_POS2),
                ],
            ),
            R::EquivNeg1 | R::EquivNeg2 => push_for_op(
                "=",
                vec![
                    template("equiv_neg1", EQUIV_NEG1),
                    template("equiv_neg2", EQUIV_NEG2),
                ],
            ),
            R::ItePos1 | R::ItePos2 => push_for_op(
                "ite",
                vec![
                    template("ite_pos1", ITE_POS1),
                    template("ite_pos2", ITE_POS2),
                ],
            ),
            R::IteNeg1 | R::IteNeg2 => push_for_op(
                "ite",
                vec![
                    template("ite_neg1", ITE_NEG1),
                    template("ite_neg2", ITE_NEG2),
                ],
            ),
            // The or-family arms above try `=>` because elaboration desugars
            // an authored implication into an or-term whose printed surface is
            // the implication. Elaboration ALSO runs the other way: an
            // authored implication is STORED as `(or (not a) b)` and printed
            // as that or-term, while the tracker annotates the tautology with
            // the implication rule. `implies_pos` over a printed `or` is not
            // spec-valid Alethe — MEASURED on carcara 1.1.0: "term '(not (or
            // ...))' is of the wrong form, expected '(not(=> phi_1 phi_2))'" —
            // and the spec-correct rule for the printed connective is `or_pos`
            // over the very same clause. Trying both spellings in both
            // directions is the whole point of judging on the PRINTED text:
            // which template applies is a fact about the surface, not about
            // the name the term store happens to carry.
            R::ImpliesPos => {
                push_for_op("=>", vec![template("implies_pos", IMPLIES_POS)]);
                if let Some(ops) = split_application(&source_str, "or") {
                    let mut lits = vec![Source(true)];
                    lits.extend(n_ary_positions(ops.len()).map(|i| Operand(i, false)));
                    positional.push((ops, "or_pos", lits, usize::MAX));
                }
            }
            R::ImpliesNeg1 | R::ImpliesNeg2 => {
                push_for_op(
                    "=>",
                    match rule {
                        R::ImpliesNeg1 => vec![template("implies_neg1", IMPLIES_NEG1)],
                        _ => vec![template("implies_neg2", IMPLIES_NEG2)],
                    },
                );
                // `(cl (=> a b) a)` over the or-surface is `or_neg` at
                // position 0 plus the `not_not` bridge the machinery already
                // emits for a double-negation-stripped literal; `(cl (=> a b)
                // (not b))` is `or_neg` at position 1 outright.
                if let Some(ops) = split_application(&source_str, "or") {
                    let ops_bytes: u64 = ops.iter().map(|o| o.len() as u64).sum();
                    self.charge(ops_bytes.saturating_mul(ops.len() as u64));
                    if self.work_budget_exhausted() {
                        return SurfaceTautology::Unjudged;
                    }
                    for k in n_ary_positions(ops.len()) {
                        positional.push((
                            ops.clone(),
                            "or_neg",
                            vec![Source(false), Operand(k, true)],
                            k,
                        ));
                    }
                }
            }
            _ => return SurfaceTautology::Unjudged,
        }
        for (ops, t) in candidates {
            positional.push((ops, t.rule, t.lits.to_vec(), usize::MAX));
        }

        // The printed traced clause, as literal strings.
        let printed: Vec<String> = self.format_derived_clause_literals(clause);
        let mut printed_sorted = printed.clone();
        printed_sorted.sort_unstable();

        for (ops, rule_name, lits, position) in positional {
            // Instantiating a template copies roughly the operand bytes;
            // stop matching once the emission budget is gone (#A2b).
            self.charge(ops.iter().map(|o| o.len() as u64).sum());
            if self.work_budget_exhausted() {
                return SurfaceTautology::Unjudged;
            }
            // Instantiate the template over the printed operands.
            let mut spec: Vec<String> = Vec::with_capacity(lits.len());
            let mut final_lits: Vec<String> = Vec::with_capacity(lits.len());
            let mut bridges: Vec<Bridge> = Vec::new();
            let mut ok = true;
            for lit in &lits {
                let (s, f) = match *lit {
                    Source(false) => (source_str.clone(), source_str.clone()),
                    Source(true) => {
                        let s = format!("(not {source_str})");
                        (s.clone(), s)
                    }
                    Operand(i, false) => match ops.get(i) {
                        Some(op) => {
                            // The spec operand prints one orientation of an
                            // arithmetic order and the traced literal the
                            // other. Same atom, two spellings; bridge it.
                            let reversed = surface_literal::surface_order_orientation_twin(op)
                                .filter(|reversed| printed.iter().any(|lit| lit == reversed));
                            match reversed {
                                Some(reversed) if !printed.iter().any(|lit| lit == op) => {
                                    match order_orientation_bridge_clause(op, &reversed) {
                                        Some(bridge_clause) => {
                                            bridges
                                                .push(Bridge::OrderOrientation { bridge_clause });
                                            (op.clone(), reversed)
                                        }
                                        None => (op.clone(), op.clone()),
                                    }
                                }
                                _ => (op.clone(), op.clone()),
                            }
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    },
                    Operand(i, true) => match ops.get(i) {
                        Some(op) => {
                            let s = format!("(not {op})");
                            match op.strip_prefix("(not ").and_then(|r| r.strip_suffix(')')) {
                                // Negating a `(not x)` operand: the traced
                                // literal is the stripped `x`; bridge it.
                                Some(inner) if printed.iter().any(|lit| lit == inner) => {
                                    bridges.push(Bridge::NotNot {
                                        spec_lit: s.clone(),
                                        inner: inner.to_string(),
                                    });
                                    (s, inner.to_string())
                                }
                                Some(_) => (s.clone(), s),
                                None => {
                                    let dual = surface_order_negation(op)
                                        .filter(|dual| printed.iter().any(|lit| lit == dual));
                                    // Same atom, other orientation, under the
                                    // negation this template already applies.
                                    let reversed = surface_order_reversal(op).filter(|reversed| {
                                        let negated = format!("(not {reversed})");
                                        printed.contains(&negated)
                                    });
                                    if printed.iter().any(|lit| lit == &s) {
                                        (s.clone(), s)
                                    } else if let Some(dual) = dual {
                                        bridges.push(Bridge::LinearOrder {
                                            operand: op.clone(),
                                            dual: dual.clone(),
                                        });
                                        (s, dual)
                                    } else if let Some(bridge_clause) =
                                        reversed.as_ref().and_then(|reversed| {
                                            order_orientation_bridge_clause(
                                                &s,
                                                &format!("(not {reversed})"),
                                            )
                                        })
                                    {
                                        let traced =
                                            format!("(not {})", reversed.unwrap_or_default());
                                        bridges.push(Bridge::OrderOrientation { bridge_clause });
                                        (s, traced)
                                    } else {
                                        (s.clone(), s)
                                    }
                                }
                            }
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    },
                };
                spec.push(s);
                final_lits.push(f);
            }
            if !ok {
                continue;
            }
            let mut final_sorted = final_lits.clone();
            final_sorted.sort_unstable();
            if final_sorted != printed_sorted {
                continue;
            }

            let args_str = match (rule_name, position) {
                ("or_neg" | "and_pos", k) if k != usize::MAX => format!(" :args ({k})"),
                _ => String::new(),
            };

            if bridges.is_empty() {
                // Already exactly what the default rendering prints? Keep the
                // default path (byte-stability for untouched proofs).
                let default_args = match rule {
                    R::AndPos(i) => format!(" :args ({i})"),
                    R::OrNeg => self
                        .infer_or_neg_position(clause, args)
                        .map(|p| format!(" :args ({p})"))
                        .unwrap_or_default(),
                    _ => String::new(),
                };
                if spec == printed && rule_name == rule.to_string() && args_str == default_args {
                    return SurfaceTautology::DefaultIsExact;
                }
                return SurfaceTautology::Rendered(format!(
                    "(step {id} (cl {}) :rule {rule_name}{args_str})",
                    spec.join(" ")
                ));
            }

            // Honest tautology + not_not bridges + resolution back to the
            // traced clause under this step's own id.
            let mut out = format!(
                "(step {id}a (cl {}) :rule {rule_name}{args_str})\n",
                spec.join(" ")
            );
            let mut premises = format!("{id}a");
            for (j, bridge) in bridges.iter().enumerate() {
                match bridge {
                    Bridge::NotNot { spec_lit, inner } => {
                        let _ = std::fmt::Write::write_fmt(
                            &mut out,
                            format_args!(
                                "(step {id}b{j} (cl (not {spec_lit}) {inner}) :rule not_not)\n"
                            ),
                        );
                    }
                    Bridge::LinearOrder { operand, dual } => {
                        let _ = std::fmt::Write::write_fmt(
                            &mut out,
                            format_args!(
                                "(step {id}b{j} (cl {operand} {dual}) :rule la_generic :args (1 1))\n"
                            ),
                        );
                    }
                    Bridge::OrderOrientation { bridge_clause } => {
                        let _ = std::fmt::Write::write_fmt(
                            &mut out,
                            format_args!(
                                "(step {id}b{j} (cl {bridge_clause}) :rule la_generic :args (1 1))\n"
                            ),
                        );
                    }
                }
                let _ = std::fmt::Write::write_fmt(&mut premises, format_args!(" {id}b{j}"));
            }
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {id} {} :rule resolution :premises ({premises}))",
                    self.format_clause(clause)
                ),
            );
            return SurfaceTautology::Rendered(out);
        }
        // Every template over the PRINTED surface has been tried and none
        // reproduces this clause. The default rendering below the call site
        // would therefore name a rule the printed step does not instantiate.
        SurfaceTautology::NoMatch
    }

    /// Honest surface derivation for an internally checked `and_pos` whose
    /// canonical conjunction prints as the authored `not (A => B)`.
    ///
    /// The traced projection is `not S or child`, with `S` the canonicalized
    /// conjunction and surface spelling `(not (=> A B))`.  Alethe cannot apply
    /// `and_pos` to that printed source.  Instead:
    ///
    /// * `not_simplify` proves `not S = (=> A B)` at the printed surface;
    /// * `equiv_pos1` exposes the usable implication literal;
    /// * `implies_neg1` or `implies_neg2` derives the corresponding component;
    /// * when `child` is inside a conjunctive `A`, a real `and_pos` projects it;
    /// * resolution restores the exact traced clause under the original id.
    ///
    /// Every match is against the fully printed strings.  Any reordered,
    /// malformed, or unrelated override declines and the caller fails loud on
    /// the unrepairable `and_pos` surface mismatch.
    fn format_not_implies_and_pos(
        &self,
        id: ProofId,
        clause: &[TermId],
        source_str: &str,
    ) -> Option<String> {
        if clause.len() != 2 {
            return None;
        }
        let mut outer = split_application(source_str, "not")?;
        if outer.len() != 1 {
            return None;
        }
        let implication = outer.pop()?;
        let (antecedent, consequent) = split_binary_implies(&implication)?;
        let not_source = format!("(not {source_str})");
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        let child = printed.iter().find(|lit| **lit != not_source)?.clone();
        let mut expected = vec![not_source.clone(), child.clone()];
        let mut actual = printed.clone();
        expected.sort_unstable();
        actual.sort_unstable();
        if actual != expected {
            return None;
        }

        let (component_steps, component_id) = if child == antecedent {
            (
                format!("(step {id}.imp (cl {implication} {antecedent}) :rule implies_neg1)\n"),
                format!("{id}.imp"),
            )
        } else if child == format!("(not {consequent})") {
            (
                format!(
                    "(step {id}.imp (cl {implication} (not {consequent})) :rule implies_neg2)\n"
                ),
                format!("{id}.imp"),
            )
        } else {
            let conjuncts = split_application(&antecedent, "and")?;
            let position = conjuncts.iter().position(|conjunct| conjunct == &child)?;
            (
                format!(
                    "(step {id}.imp (cl {implication} {antecedent}) :rule implies_neg1)\n\
                     (step {id}.part (cl (not {antecedent}) {child}) :rule and_pos :args ({position}))\n\
                     (step {id}.component (cl {implication} {child}) :rule resolution :premises ({id}.imp {id}.part))\n"
                ),
                format!("{id}.component"),
            )
        };

        let equivalence = format!("(= {not_source} {implication})");
        Some(format!(
            "(step {id}.ns (cl {equivalence}) :rule not_simplify)\n\
             (step {id}.eq (cl (not {equivalence}) {not_source} (not {implication})) :rule equiv_pos1)\n\
             {component_steps}\
             (step {id}.surface (cl {not_source} (not {implication})) :rule resolution :premises ({id}.ns {id}.eq))\n\
             (step {id} {} :rule resolution :premises ({id}.surface {component_id}))",
            self.format_clause(clause)
        ))
    }

    /// Honest premise-free derivation of an `or_pos` tautology whose source
    /// term prints as the De Morgan surface `(not (and A1 .. An))`:
    ///
    ///   {id}a (cl (= (not S) (and A..)))            not_simplify (S = ¬(and A..))
    ///   {id}b (cl (not {id}a-eq) (not S) (not (and A..)))  equiv_pos1
    ///   {id}c (cl (and A..) (not A1) .. (not An))   and_neg
    ///   {id}  (cl (not S) (not A1) .. (not An))     resolution (a b c)
    ///
    /// Two further spellings of that same surface occur in the corpus, and
    /// BOTH appear on the QF_UF/QG-classification family, where they made this
    /// bridge decline and shipped the default `or_pos` that carcara refuses
    /// with "term '(not (not (and ...)))' is of the wrong form, expected
    /// '(not(or ...))'" — an `invalid` document, not a holey one:
    ///
    /// * the printed `and` is a NESTED binary spine (the authored assertion was
    ///   written that way), so ONE `and_neg` yields two negated operands rather
    ///   than n. The repair is the shared printed-nesting walk
    ///   [`Self::navigate_and_pos_gate`] already uses: one genuine `and_neg`
    ///   per printed node, resolved together. No printed TERM changes, so the
    ///   `assume` that has to keep matching the problem premise is untouched.
    /// * an individual conjunct is spelled with its equality arguments in the
    ///   opposite order from the traced literal — the surface override carries
    ///   the AUTHORED orientation while the traced literal carries the
    ///   canonical term. `eq_symmetric` + `equiv_pos1` re-orients exactly that
    ///   literal, which is a real (if trivial) inference rather than a
    ///   relabelling.
    ///
    /// Taken only when every printed leaf pairs with a distinct traced literal
    /// under one of those two spellings and nothing in the traced clause is
    /// left over; `None` keeps the default rendering, and the caller's
    /// fail-loud gate then refuses to ship it.
    fn format_not_and_or_pos(
        &self,
        id: ProofId,
        clause: &[TermId],
        source_str: &str,
    ) -> Option<String> {
        let (and_str, _) = split_not_and_full(source_str)?;
        self.charge(and_str.len() as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        let nesting = PrintedNesting::build(&and_str, "and", PRINTED_NESTING_NODE_BUDGET)?;
        let not_source = format!("(not {source_str})");
        let printed: Vec<String> = self.format_derived_clause_literals(clause);
        if self.work_budget_exhausted() {
            return None;
        }

        // Account for every traced literal exactly once: the gate literal, then
        // one per printed leaf. A leftover literal means the printed surface
        // does not describe this clause, and the bridge must decline.
        let mut unclaimed: Vec<Option<&str>> = printed.iter().map(|l| Some(l.as_str())).collect();
        let gate = unclaimed
            .iter()
            .position(|literal| *literal == Some(not_source.as_str()))?;
        unclaimed[gate] = None;
        let mut reversed: Vec<(String, String)> = Vec::new();
        for leaf in &nesting.leaves {
            let exact = format!("(not {leaf})");
            if let Some(slot) = unclaimed
                .iter()
                .position(|literal| *literal == Some(exact.as_str()))
            {
                unclaimed[slot] = None;
                continue;
            }
            // Only an equality may differ from its traced literal by argument
            // order, and only in that one way; anything else is a decline.
            let swapped = surface_equality_reversal(leaf)?;
            let flipped = format!("(not {swapped})");
            let slot = unclaimed
                .iter()
                .position(|literal| *literal == Some(flipped.as_str()))?;
            unclaimed[slot] = None;
            reversed.push((leaf.clone(), swapped));
        }
        if unclaimed.iter().any(Option::is_some) {
            return None;
        }

        let eq = format!("(= {not_source} {and_str})");
        let mut out = String::new();
        let mut premises: Vec<String> = Vec::with_capacity(nesting.nodes.len() + 2);
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id}a (cl {eq}) :rule not_simplify)\n\
                 (step {id}b (cl (not {eq}) {not_source} (not {and_str})) :rule equiv_pos1)\n"
            ),
        );
        premises.push(format!("{id}a"));
        premises.push(format!("{id}b"));
        // One `and_neg` per printed node, outermost first. A flat print has a
        // single node, so this reduces to the original three-step bridge byte
        // for byte.
        for (node, operands) in nesting.operands.iter().enumerate() {
            let node_id = if node == 0 {
                format!("{id}c")
            } else {
                format!("{id}c{node}")
            };
            let negated: Vec<String> = operands.iter().map(|op| format!("(not {op})")).collect();
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {node_id} (cl {} {}) :rule and_neg)\n",
                    nesting.nodes[node],
                    negated.join(" ")
                ),
            );
            premises.push(node_id);
        }
        // `(cl A (not A-reversed))`: resolved against the `and_neg` chain this
        // rewrites the one literal whose equality is spelled the other way
        // round, and leaves every other literal alone.
        for (index, (leaf, swapped)) in reversed.iter().enumerate() {
            let symmetry = format!("(= {leaf} {swapped})");
            let taut_id = format!("{id}s{index}");
            let bridge_id = format!("{id}s{index}b");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {taut_id} (cl {symmetry}) :rule eq_symmetric)\n\
                     (step {bridge_id} (cl (not {symmetry}) {leaf} (not {swapped})) \
                     :rule equiv_pos1)\n"
                ),
            );
            premises.push(taut_id);
            premises.push(bridge_id);
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl {}) :rule resolution :premises ({}))",
                printed.join(" "),
                premises.join(" ")
            ),
        );
        self.charge(out.len() as u64);
        if self.work_budget_exhausted() {
            return None;
        }
        Some(out)
    }

    fn is_negation_of(&self, lit: TermId, term: TermId) -> bool {
        matches!(self.terms.get(lit), TermData::Not(inner) if *inner == term)
    }
}

/// The binder name Carcara's `arrays_ext` hard-codes in its `choice` witness.
///
/// MEASURED against the pinned array-capable build: the rule compares its own
/// constructed term with `assert_polyeq`, which normalizes Int/Real subtyping
/// but does NOT quotient by alpha-renaming, so an otherwise byte-identical
/// proof using binder `zz` is rejected with "expected terms to be equal".
const EXT_CHOICE_BINDER: &str = "x";

/// Alethe's empty clause, spelled with the BARE reserved `cl` token.
///
/// AY carries the empty clause as a zero-arity `cl` application, and `drup`
/// steps ship it inside `:args`. The pinned checker lexes `cl` as clause
/// syntax, so the quoted spelling `(|cl|)` is a zero-argument application and
/// is refused at parse time; see the `TermData::App` arm of `format_term_data`.
const ALETHE_CLAUSE_CONSTRUCTOR_TERM: &str = "(cl)";

/// Node cap for the shared printed-nesting walk. A 57-deep binary `and` (the
/// mathsat `medium*` shape) needs 56 nodes; anything past this is a printing
/// pathology and must fail loud instead of emitting a huge unverified chain.
const PRINTED_NESTING_NODE_BUDGET: usize = 4096;

/// Placeholder the Skolem-collapse guard substitutes for a `choice` binder
/// before comparing two definition bodies.
///
/// Only ever appears inside a comparison key, never in emitted text, so it is
/// deliberately unspellable as an SMT-LIB symbol: a body that already mentioned
/// it could otherwise be made to collide with a different body on purpose.
const CHOICE_BINDER_NORMAL_FORM: &str = "|ay!choice-binder|";

/// Whether `needle` occurs anywhere inside `haystack` (inclusive).
fn term_mentions(terms: &TermStore, haystack: TermId, needle: TermId) -> bool {
    walk_subterms(terms, haystack, &mut |term, _| term == needle)
}

/// Whether any leaf variable inside `haystack` is spelled exactly `name`.
fn term_mentions_symbol(terms: &TermStore, haystack: TermId, name: &str) -> bool {
    walk_subterms(terms, haystack, &mut |_, data| match data {
        TermData::Var(symbol, _) => symbol == name,
        // An application HEAD wearing the binder's name is a mention too: the
        // printed `(name arg…)` is a parse error inside `(choice ((name S)) …)`,
        // so treating it as clean would regress the document from `holey` to
        // `invalid`. Declining is fail-closed — the step stays an honest hole.
        TermData::App(Symbol::Named(symbol), _) => symbol == name,
        TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
            bindings.iter().any(|(binder, _)| binder == name)
        }
        TermData::Let(bindings, _) => bindings.iter().any(|(binder, _)| binder == name),
        _ => false,
    })
}

/// Structural walk with cycle protection; stops at the first `hit`.
fn walk_subterms(
    terms: &TermStore,
    root: TermId,
    hit: &mut dyn FnMut(TermId, &TermData) -> bool,
) -> bool {
    let mut stack = vec![root];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let data = terms.get(term);
        if hit(term, data) {
            return true;
        }
        match data {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.extend([*cond, *then_branch, *else_branch]);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            TermData::Let(bindings, body) => {
                stack.push(*body);
                stack.extend(bindings.iter().map(|(_, bound)| *bound));
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is #[non_exhaustive]: a variant added upstream must
            // not silently hide subterms from the capture/dependency scan.
            _ => return true,
        }
    }
    false
}

/// What the printed-surface spec matcher concluded about one premise-free
/// clausification (“tautologous rule”) step.
///
/// The whole point of this type is that the printer's two possible reasons for
/// emitting NOTHING are not the same fact, and conflating them is what let a
/// false claim ship. `format_surface_tautology` used to return `None` both when
/// the default rendering was already the exact spec instance *and* when no spec
/// instantiation over the printed surface reproduced the clause at all. The
/// first is fine; the second means the default rendering is about to name a
/// rule the PRINTED step does not instantiate, which is what the external
/// checker refuses.
enum SurfaceTautology {
    /// Not judged. The rule is outside the family, the source term could not
    /// be identified, or the #A2b emission work budget ran out mid-match — in
    /// every case the printed surface says nothing about validity and the
    /// caller must not conclude anything from it.
    Unjudged,
    /// The DEFAULT rendering is already the exact spec instance over the
    /// printed surface. Keep it, byte for byte.
    DefaultIsExact,
    /// Replacement text that IS a spec instance over the printed surface.
    Rendered(String),
    /// No spec template over the printed surface reproduces this clause.
    NoMatch,
}

/// How the surface override channel relates the PRINTED clause to the term DAG.
///
/// The evidence-sensitive wire promotions ([`crate::promoted_wire_rule`])
/// reason about the internal term DAG, while an override changes the text the
/// external checker reads. What makes a promotion safe is therefore not the
/// ABSENCE of the channel but its irrelevance HERE.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClauseSurfaceAgreement {
    /// The clause renders byte-identically with and without the channel, so
    /// the checker reads exactly the text the validators reasoned about.
    Identical,
    /// Every override the clause reaches is either the identity spelling or
    /// the ARGUMENT-REVERSED spelling of its own canonical rendering
    /// (`(> b a)` where the printer would write `(< a b)`), and at least one
    /// is the latter. `mk_gt`/`mk_ge` canonicalize `>`/`>=` into `<`/`<=`
    /// with the arguments swapped, so this is exactly the authored spelling of
    /// a canonicalized order atom — the printed text is a different byte
    /// string denoting the SAME atom, not a different formula.
    OrderReversed,
    /// At least one reachable override is the exact argument-reversed spelling
    /// of its canonical binary equality, and every other override is an
    /// identity spelling, another equality symmetry, or [`Self::OrderReversed`]
    /// comparison converse. Equality is the same Boolean atom under symmetry,
    /// but its signed `la_generic` row orientation changes; callers must replay
    /// the effective printed certificate before publishing numeric evidence.
    EqualityReversed,
    /// At least one reachable override differs from its canonical rendering
    /// only by exact linear respellings (`linear_respelling.rs`: the lenient
    /// `-2` for `(- 2)`, a literal-zero summand), possibly under a converse
    /// order spelling, and every other override is one of the classes above.
    /// The printed atom is the same atom, but pinned Carcara parses the two
    /// spellings as different terms, so callers replay the effective printed
    /// certificate before publishing numeric evidence, exactly as for
    /// [`Self::EqualityReversed`].
    LinearRespelled,
    /// The channel changes what the clause says.
    Divergent,
}

/// Classify the surface override channel's effect on this exact clause.
///
/// Screening the whole document instead — refusing every promotion whenever
/// any override is installed anywhere — discards checkable evidence for
/// clauses the channel never touches. A composed authored root installs
/// overrides for its own spelling, and that alone downgraded independently
/// checked steps such as `(= (+ 2 3) 5)` to `hole`.
///
/// [`ClauseSurfaceAgreement::OrderReversed`] and
/// [`ClauseSurfaceAgreement::EqualityReversed`] are not weaker barriers, but
/// stronger same-atom classifications: byte-equality is replaced only by the
/// exact converse spelling AY's order constructors canonicalize or the exact
/// symmetry of a binary equality. The former adds no reliance on a model of
/// external arithmetic — the same converse identity is already load-bearing
/// in this file, where [`surface_order_reversal`] drives the `comp_simplify`
/// congruence bridge. The latter remains distinguished because a signed
/// equality row must be replayed against its effective orientation.
///
/// This is deliberately the ONE classifier: the printer and the publication
/// wire-gap gate both reach it through shared wire-promotion predicates, so
/// neither can drift from the other. `evaluate` and the separately checked BV
/// intrinsic lowerings admit parser-identical literal spellings; other callers
/// keep `literal_respellings = false`. See `surface_literal::spelled_alike`.
pub(crate) fn clause_surface_agreement_admitting(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    literal_respellings: bool,
) -> ClauseSurfaceAgreement {
    let Some(overrides) = term_overrides else {
        return ClauseSurfaceAgreement::Identical;
    };
    if overrides.is_empty() {
        return ClauseSurfaceAgreement::Identical;
    }
    // Cheap NECESSARY condition first. `format_term` memoizes only WITHIN one
    // printer, so rendering a clause through two fresh printers is superlinear
    // in term size — and this predicate sits on a hot path, because
    // `proof_has_known_wire_gap` runs it over every stored step. If the channel
    // maps nothing this clause mentions, the two renderings are identical by
    // construction and no rendering is needed to know it.
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut seen = HashSet::default();
    let mut reached: Vec<TermId> = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if overrides.contains_key(&term) {
            reached.push(term);
            // An override REPLACES the rendering of its term, so the printer
            // never recurses past it; neither does this walk.
            continue;
        }
        stack.extend(terms.children(term));
    }
    if reached.is_empty() {
        return ClauseSurfaceAgreement::Identical;
    }
    // A reachable entry may still be an IDENTITY spelling. Compare each entry
    // against its own override-free rendering instead of re-rendering the whole
    // clause twice: an override that reproduces exactly what its term already
    // prints cannot change any text mentioning it. One shared printer memoizes
    // across the walk. This is conservative where it differs — a nested entry
    // shadowed by an outer one is reported as changed — and conservative here
    // means withholding the promotion.
    //
    // A witness resugared to its `choice` term is the SAME atom everywhere:
    // rendering a constant as one closed term at every occurrence is a global
    // substitution, which preserves every rule instance the document contains
    // (`prepare_array_extensionality_choices` and the certified Skolem lane
    // both rest on that). Such an entry is keyed by a `Var` and spells a
    // `(choice ..)`; it is never a divergence, and the comparison printer
    // spells the witness the same way so an entry over a term that MENTIONS
    // the witness is compared against a canonical rendering that also does
    // — otherwise the eighth shape's `(>= (g c) c)` would read as divergent
    // from `(<= sk (g sk))` by the witness's spelling alone.
    let printer = AlethePrinter::new(terms);
    let mut witness_spellings: HashSet<TermId> = HashSet::default();
    for (&term, surface) in overrides {
        if matches!(terms.get(term), TermData::Var(..)) && surface.starts_with("(choice ") {
            printer
                .skolem_overrides
                .borrow_mut()
                .insert(term, surface.clone());
            witness_spellings.insert(term);
        }
    }
    let mut agreement = ClauseSurfaceAgreement::Identical;
    for term in reached {
        if witness_spellings.contains(&term) {
            continue;
        }
        let Some(surface) = overrides.get(&term) else {
            return ClauseSurfaceAgreement::Divergent;
        };
        let canonical = printer.format_term(term);
        if surface_literal::spelled_alike(surface, &canonical, literal_respellings) {
            continue;
        }
        // The authored `>`/`>=` spelling of a canonicalized `<`/`<=` atom.
        // `surface_order_reversal` swaps the two ARGUMENT SUBSTRINGS and maps
        // the operator to its converse, so a match means the override's
        // arguments are byte-for-byte the canonical rendering's own arguments
        // and only the converse spelling differs. It cannot hide a re-spelled
        // operand, and it cannot cross strictness (`(>= x 0)` reverses to
        // `(<= 0 x)`, never to `(< 0 x)`).
        if surface_order_reversal(surface).is_some_and(|reversed| reversed == canonical) {
            if agreement == ClauseSurfaceAgreement::Identical {
                agreement = ClauseSurfaceAgreement::OrderReversed;
            }
            continue;
        }
        // The same atom up to exact linear respellings, possibly under the
        // converse order spelling: replay-gated, like a reversed equality.
        let linear =
            |surface: &str| linear_respelling::equal_modulo_linear_respelling(surface, &canonical);
        if linear(surface)
            || surface_order_reversal(surface).is_some_and(|reversed| linear(&reversed))
        {
            if agreement != ClauseSurfaceAgreement::EqualityReversed {
                agreement = ClauseSurfaceAgreement::LinearRespelled;
            }
            continue;
        }
        // Equality is symmetric as a Boolean atom, but reversing its operands
        // reverses the signed arithmetic row an external `la_generic` checker
        // builds. Preserve that distinction so the Farkas gate can demand a
        // bounded replay of the exact effective certificate.
        if surface_equality_reversal(surface).is_some_and(|reversed| reversed == canonical) {
            if agreement != ClauseSurfaceAgreement::LinearRespelled {
                agreement = ClauseSurfaceAgreement::EqualityReversed;
            }
            continue;
        }
        return ClauseSurfaceAgreement::Divergent;
    }
    agreement
}

/// Compute the exact override channel visible to downstream wire rules after
/// bounded authored-assume planning confines supported consumed spellings and
/// all wholly unused assumption spellings to their own `assume` commands.
///
/// This runs the same planner the Alethe printer runs before emission. An
/// An unsupported spelling with any consumed `Assume` id remains in the
/// returned map and therefore remains subject to the ordinary fail-closed
/// surface gate; a planning error is returned rather than silently hiding an
/// override. A document with authored surfaces plans through
/// [`crate::effective_wire_term_overrides_for_authored_proof`] instead.
pub fn effective_wire_term_overrides_for_proof(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
    AlethePrinter::new_with_overrides(terms, term_overrides).planned_wire_term_overrides(proof)
}

/// Whether an exact authored `let` spelling takes the printer's fully checked
/// elimination arm rather than its visible `hole` fallback.
///
/// The terminal wire-policy gate calls this over the same effective override
/// map used by emission. Keeping the decision here prevents strict proof mode
/// from rejecting a bridge the printer can certify—or accepting a `let` whose
/// normalization would still require a hole. A local work cap makes this a
/// conservative preflight for unusually large term DAGs.
#[must_use]
pub fn certified_let_assume_bridge_is_supported(
    terms: &TermStore,
    term: TermId,
    surface: &str,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    const PREFLIGHT_WORK_BUDGET: u64 = 4 * 1024 * 1024;
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        term_overrides,
        Some(PREFLIGHT_WORK_BUDGET),
    );
    printer
        .plan_let_assume_bridge(term, surface)
        .is_some_and(|plan| plan.is_certified())
}

/// Split a surface-override string of the form `(=> A B)` into (`A`, `B`)
/// by balanced-token scanning. Returns `None` for anything that is not
/// exactly a binary `=>` application.
fn split_binary_implies(s: &str) -> Option<(String, String)> {
    let mut tokens = split_application(s, "=>")?;
    if tokens.len() == 2 {
        let b = tokens.pop()?;
        let a = tokens.pop()?;
        Some((a, b))
    } else {
        None
    }
}

/// Exact SMT-LIB surface duals used by arithmetic-order normalization.
fn surface_strings_are_complements(left: &str, right: &str) -> bool {
    if split_application(left, "not").is_some_and(|args| args.len() == 1 && args[0] == right)
        || split_application(right, "not").is_some_and(|args| args.len() == 1 && args[0] == left)
    {
        return true;
    }

    surface_order_negation(left).is_some_and(|dual| dual == right)
        || surface_order_negation(right).is_some_and(|dual| dual == left)
}

/// Surface spelling of the exact negation of a binary arithmetic order.
fn surface_order_negation(s: &str) -> Option<String> {
    for (op, dual) in [("<=", "<"), ("<", "<="), (">=", ">"), (">", ">=")] {
        if let Some(args) = split_application(s, op) {
            if args.len() == 2 {
                return Some(format!("({dual} {} {})", args[1], args[0]));
            }
        }
    }
    None
}

/// THE order-orientation device, in one place: the clause that lets a
/// resolution replace one printed orientation of an arithmetic order atom with
/// the other.
///
/// `(>= a 10)` and `(<= 10 a)` are ONE atom to AY's order constructors and two
/// distinct terms to the checker. The printer cannot canonicalize one of them
/// away, because an `assume` must print the orientation the PROBLEM FILE
/// authored — the checker parses the `.smt2` alongside the proof and compares
/// the two textually. So both spellings necessarily coexist in one document,
/// and every rule that requires textual agreement between two occurrences of
/// that atom can refuse a step AY genuinely derived.
///
/// The faithful repair is not to relabel the step and not to pick a spelling by
/// fiat: it is to STATE the orientation identity and let the checker verify it.
/// The identity is a two-literal linear-arithmetic tautology — the COMPLEMENT
/// of the literal being discharged beside the literal being introduced — so
/// `la_generic :args (1 1)` proves it, and a false one is refused ("final
/// disequality is not contradictory").
///
/// `spec` is the literal the surrounding inference states; `traced` the literal
/// the document must end up with. `None` unless the two are exactly one atom in
/// its two spellings, under at most a shared negation.
fn order_orientation_bridge_clause(spec: &str, traced: &str) -> Option<String> {
    let strip = |s: &str| -> Option<String> {
        split_application(s, "not").and_then(|inner| (inner.len() == 1).then(|| inner[0].clone()))
    };
    match (strip(spec), strip(traced)) {
        (Some(spec_atom), Some(traced_atom)) => (surface_order_reversal(&spec_atom).as_deref()
            == Some(traced_atom.as_str()))
        .then(|| format!("{spec_atom} (not {traced_atom})")),
        (None, None) => (surface_order_reversal(spec).as_deref() == Some(traced))
            .then(|| format!("(not {spec}) {traced}")),
        _ => None,
    }
}

/// Where a premise-free tautologous rule states its own source term: the
/// polarity it appears at in the step's clause, and the head symbols its
/// printed surface may legitimately carry.
///
/// This is what lets [`AlethePrinter::format_surface_tautology`] judge a step
/// whose producer set no source argument, instead of waving it through. Every
/// rule here concludes a clause that MENTIONS its source — that is what makes
/// these rules premise-free — so the clause is a complete and authoritative
/// place to look for it.
///
/// The head sets carry the surface spellings elaboration can leave behind:
/// an `or`-family source may print as the authored `=>` it was desugared from,
/// or as the De Morgan `(not (and ...))` it was rewritten from. `None` means
/// the rule is outside the family and the predicate must stay silent about it.
fn surface_tautology_source_signature(
    rule: &ay_core::AletheRule,
) -> Option<(
    bool, /* source appears negated */
    &'static [&'static str],
)> {
    use ay_core::AletheRule as R;
    const OR_HEADS: &[&str] = &["or", "=>", "not"];
    const AND_HEADS: &[&str] = &["and"];
    const XOR_HEADS: &[&str] = &["xor"];
    const EQ_HEADS: &[&str] = &["="];
    const ITE_HEADS: &[&str] = &["ite"];
    // Both spellings, both directions: an authored `=>` may be stored as an
    // or-term and printed as one, exactly as an or-term may be printed back as
    // the `=>` it was desugared from.
    const IMPLIES_HEADS: &[&str] = &["=>", "or"];
    Some(match rule {
        R::OrPos(_) => (true, OR_HEADS),
        R::OrNeg => (false, OR_HEADS),
        R::AndPos(_) => (true, AND_HEADS),
        R::AndNeg => (false, AND_HEADS),
        R::XorPos1 | R::XorPos2 => (true, XOR_HEADS),
        R::XorNeg1 | R::XorNeg2 => (false, XOR_HEADS),
        R::EquivPos1 | R::EquivPos2 => (true, EQ_HEADS),
        R::EquivNeg1 | R::EquivNeg2 => (false, EQ_HEADS),
        R::ItePos1 | R::ItePos2 => (true, ITE_HEADS),
        R::IteNeg1 | R::IteNeg2 => (false, ITE_HEADS),
        R::ImpliesPos => (true, IMPLIES_HEADS),
        R::ImpliesNeg1 | R::ImpliesNeg2 => (false, IMPLIES_HEADS),
        _ => return None,
    })
}

/// Equivalent argument-reversed spelling of a binary arithmetic order.
fn surface_order_reversal(s: &str) -> Option<String> {
    for (op, reversed) in [("<=", ">="), ("<", ">"), (">=", "<="), (">", "<")] {
        if let Some(args) = split_application(s, op) {
            if args.len() == 2 {
                return Some(format!("({reversed} {} {})", args[1], args[0]));
            }
        }
    }
    None
}

/// Exact symmetric spelling of a binary equality.
fn surface_equality_reversal(s: &str) -> Option<String> {
    let args = split_application(s, "=")?;
    (args.len() == 2).then(|| format!("(= {} {})", args[1], args[0]))
}

/// The head symbol of a printed application, or `None` when `s` is not one
/// (a bare symbol, a numeral, an unbalanced rendering).
///
/// Tokenized rather than split on whitespace so a quoted `|sym with spaces|`
/// head and nested-application arguments are both handled.
fn printed_head_symbol(s: &str) -> Option<String> {
    let inner = s.strip_prefix('(')?.strip_suffix(')')?;
    split_sexpr_tokens(inner)?.into_iter().next()
}

fn surface_order_operator(s: &str) -> Option<&'static str> {
    ["<=", "<", ">=", ">"]
        .into_iter()
        .find(|operator| split_application(s, operator).is_some())
}

/// Split a rendered single-binder quantifier into its binder token and body.
///
/// The binder sort may itself be an indexed/application sort, so both the
/// quantifier arguments and binding fields are scanned as balanced SMT-LIB
/// terms instead of split on whitespace.
fn split_single_binder_quantifier(s: &str, keyword: &str) -> Option<(String, String)> {
    let mut args = split_application(s, keyword)?;
    if args.len() != 2 {
        return None;
    }
    let body = args.pop()?;
    let bindings = args.pop()?;
    let binding_terms = split_smt_terms(bindings.strip_prefix('(')?.strip_suffix(')')?)?;
    let [binding] = binding_terms.as_slice() else {
        return None;
    };
    let fields = split_smt_terms(binding.strip_prefix('(')?.strip_suffix(')')?)?;
    let [binder, _sort] = fields.as_slice() else {
        return None;
    };
    Some((binder.clone(), body))
}

/// Walk the symbol tokens of one rendered term, in order, as byte spans and
/// without allocating: string literals and delimiters are skipped, a quoted
/// symbol is yielded with its bars. Same tokenization as
/// [`substitute_smt_symbol`]. Stops early when `visit` returns `false`.
fn for_each_symbol_token_span(input: &str, mut visit: impl FnMut(usize, usize) -> bool) {
    let bytes = input.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => {
                index += 1;
                while index < bytes.len() {
                    if bytes[index] == b'"' {
                        if bytes.get(index + 1) == Some(&b'"') {
                            index += 2;
                            continue;
                        }
                        index += 1;
                        break;
                    }
                    index += 1;
                }
            }
            b'|' => {
                let start = index;
                index += 1;
                while index < bytes.len() && bytes[index] != b'|' {
                    index += 1;
                }
                if index < bytes.len() {
                    index += 1;
                }
                if !visit(start, index) {
                    return;
                }
            }
            b'(' | b')' => index += 1,
            byte if byte.is_ascii_whitespace() => index += 1,
            _ => {
                let start = index;
                while index < bytes.len()
                    && !bytes[index].is_ascii_whitespace()
                    && !matches!(bytes[index], b'(' | b')' | b'"' | b'|')
                {
                    index += 1;
                }
                if !visit(start, index) {
                    return;
                }
            }
        }
    }
}

/// The first symbol token of `input` that names a member of `names`, if any.
/// `|x|` and `x` are one symbol to every SMT-LIB reader, so a quoted token is
/// looked up by its contents.
pub(crate) fn first_symbol_token_in<'a>(
    input: &str,
    names: &'a HashSet<String>,
) -> Option<&'a String> {
    let mut found = None;
    for_each_symbol_token_span(input, |start, end| {
        let token = &input[start..end];
        let bare = token
            .strip_prefix('|')
            .and_then(|t| t.strip_suffix('|'))
            .unwrap_or(token);
        found = names.get(bare);
        found.is_none()
    });
    found
}

/// Replace every symbol token that is a key of `spelling` by its value, in
/// one pass with [`substitute_smt_symbol`]'s tokenization. `None` when no
/// token matched, so an unchanged rendering costs no allocation.
fn respell_symbol_tokens(input: &str, spelling: &HashMap<String, String>) -> Option<String> {
    let mut output: Option<String> = None;
    let mut copied = 0usize;
    for_each_symbol_token_span(input, |start, end| {
        if let Some(replacement) = spelling.get(&input[start..end]) {
            let out = output.get_or_insert_with(|| String::with_capacity(input.len()));
            out.push_str(&input[copied..start]);
            out.push_str(replacement);
            copied = end;
        }
        true
    });
    let mut out = output?;
    out.push_str(&input[copied..]);
    Some(out)
}

/// Replace one SMT-LIB symbol token without touching strings, quoted-symbol
/// contents, or longer identifiers. The certified Skolem lane is restricted to
/// quantifier-free bodies, so no nested binder can shadow the selected token.
fn substitute_smt_symbol(input: &str, target: &str, replacement: &str) -> String {
    let chars: Vec<char> = input.chars().collect();
    let mut output = String::with_capacity(input.len().saturating_add(replacement.len()));
    let mut index = 0usize;
    while index < chars.len() {
        if chars[index] == '"' {
            let start = index;
            index += 1;
            while index < chars.len() {
                if chars[index] == '"' {
                    // SMT-LIB escapes a quote inside a string by doubling it.
                    if index + 1 < chars.len() && chars[index + 1] == '"' {
                        index += 2;
                        continue;
                    }
                    index += 1;
                    break;
                }
                index += 1;
            }
            output.extend(chars[start..index].iter());
            continue;
        }
        if chars[index] == '|' {
            let start = index;
            index += 1;
            while index < chars.len() && chars[index] != '|' {
                index += 1;
            }
            if index < chars.len() {
                index += 1;
            }
            let token: String = chars[start..index].iter().collect();
            if token == target {
                output.push_str(replacement);
            } else {
                output.push_str(&token);
            }
            continue;
        }
        if chars[index].is_whitespace() || matches!(chars[index], '(' | ')') {
            output.push(chars[index]);
            index += 1;
            continue;
        }
        let start = index;
        while index < chars.len()
            && !chars[index].is_whitespace()
            && !matches!(chars[index], '(' | ')' | '"' | '|')
        {
            index += 1;
        }
        let token: String = chars[start..index].iter().collect();
        if token == target {
            output.push_str(replacement);
        } else {
            output.push_str(&token);
        }
    }
    output
}

/// Split a rendered De Morgan surface string `(not (and A1 ... An))` into
/// the printed `(and ...)` string and its conjunct strings. Returns `None`
/// for any other shape.
fn split_not_and_full(s: &str) -> Option<(String, Vec<String>)> {
    let mut tokens = split_application(s, "not")?;
    if tokens.len() != 1 {
        return None;
    }
    let and_str = tokens.pop()?;
    let conjuncts = split_application(&and_str, "and")?;
    Some((and_str, conjuncts))
}

/// Conjunct strings of a rendered `(not (and A1 ... An))` surface string.
fn split_not_and(s: &str) -> Option<Vec<String>> {
    split_not_and_full(s).map(|(_, conjuncts)| conjuncts)
}

/// Parse a PRINTED SMT-LIB bit-vector literal into `(value, width)`.
///
/// Accepts the three surface spellings a problem file may legitimately use for
/// a bit-vector constant: `#b<bits>`, `#x<hex digits>` and `(_ bv<value>
/// <width>)`. Everything else — a variable, an application, a literal whose
/// value does not fit its declared width — returns `None`, so a caller gating
/// a lowering on this can never mistake a non-constant for a constant.
fn parse_printed_bitvec_literal(text: &str) -> Option<(num_bigint::BigUint, u32)> {
    let text = text.trim();
    if let Some(digits) = text.strip_prefix("#b") {
        if digits.is_empty() || !digits.bytes().all(|byte| matches!(byte, b'0' | b'1')) {
            return None;
        }
        let width = u32::try_from(digits.len()).ok()?;
        return Some((
            num_bigint::BigUint::parse_bytes(digits.as_bytes(), 2)?,
            width,
        ));
    }
    if let Some(digits) = text.strip_prefix("#x") {
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return None;
        }
        let width = u32::try_from(digits.len()).ok()?.checked_mul(4)?;
        return Some((
            num_bigint::BigUint::parse_bytes(digits.as_bytes(), 16)?,
            width,
        ));
    }
    let mut tokens = text
        .strip_prefix('(')?
        .strip_suffix(')')?
        .split_whitespace();
    if tokens.next()? != "_" {
        return None;
    }
    let digits = tokens.next()?.strip_prefix("bv")?;
    let width: u32 = tokens.next()?.parse().ok()?;
    if tokens.next().is_some() || digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let value = num_bigint::BigUint::parse_bytes(digits.as_bytes(), 10)?;
    (value.bits() <= u64::from(width)).then_some((value, width))
}

/// Whether a native bit-vector bit-blast lemma is in the exact bounded subset
/// for which the Alethe printer emits a checked Carcara derivation.
///
/// This is the single capability predicate shared by proof publication and
/// rendering. It invokes the same formatter dispatch, including its
/// surface-text checks and width/circuit budgets, so the terminal policy
/// cannot reject a lowering the exporter supports or admit one that would
/// fall back to `hole`.
#[must_use]
pub fn checked_bv_bitblast_lowering_supported(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    checked_bv_bitblast_lowering_supported_asking(
        terms,
        kind,
        clause,
        term_overrides,
        CompleteBlastAsk::Asked,
    )
}

/// [`checked_bv_bitblast_lowering_supported`], asking the complete bit-blast
/// only as `complete_blast` says ([`CompleteBlastAsk`]).
///
/// The support memo stores only `true`. A lane not asked, or stopped by its
/// caller, can only turn a `true` into `false`, which is never stored, so a
/// remembered answer is the one an unstopped ask gives.
#[must_use]
pub fn checked_bv_bitblast_lowering_supported_asking(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    complete_blast: CompleteBlastAsk<'_>,
) -> bool {
    if !matches!(
        kind,
        ay_core::TheoryLemmaKind::BvBitBlast | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
    ) {
        return false;
    }
    // One render per lemma answers every repeat of the question
    // (`bv_support_memo`).
    bv_support_memo::answered(terms, *kind, clause, term_overrides, || {
        bv_bitblast_support_rendered(terms, kind, clause, term_overrides, complete_blast)
    })
}

/// The render that answers [`checked_bv_bitblast_lowering_supported_asking`],
/// remembered by nothing.
fn bv_bitblast_support_rendered(
    terms: &TermStore,
    kind: &ay_core::TheoryLemmaKind,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    complete_blast: CompleteBlastAsk<'_>,
) -> bool {
    let printer = AlethePrinter::new_with_overrides(terms, term_overrides)
        .asking_complete_blast(complete_blast);
    // A question, not a render: nothing it spells reaches a document.
    dialect::discarding_notes(|| {
        (matches!(kind, ay_core::TheoryLemmaKind::BvBitBlast)
            && printer
                .format_binary_bvand_aci_simp(ProofId(0), clause)
                .is_some())
            || printer
                .format_checked_bv_bitblast_lowering(ProofId(0), clause)
                .is_some()
    })
}

pub(crate) fn format_sort_alethe(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::BitVec(bits) => format!("(_ BitVec {})", bits.width),
        Sort::Array(array) => format!(
            "(Array {} {})",
            format_sort_alethe(&array.index_sort),
            format_sort_alethe(&array.element_sort)
        ),
        Sort::String => "String".to_string(),
        Sort::RegLan => "RegLan".to_string(),
        Sort::FloatingPoint(exponent, significand) => {
            format!("(_ FloatingPoint {exponent} {significand})")
        }
        Sort::Uninterpreted(name) => quote_symbol(name),
        Sort::Datatype(datatype) => quote_symbol(&datatype.name),
        Sort::Seq(element) => format!("(Seq {})", format_sort_alethe(element)),
        Sort::Char => "Char".to_string(),
        Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => quote_symbol(name),
        _ => sort.to_string(),
    }
}

/// Why one symbol has no lossless spelling in pinned Carcara's grammar, if it
/// has none: Carcara follows standard quoted-symbol syntax, so a name carrying
/// `|` or `\` can only be written with the AY/Z3 escape extension it rejects.
fn carcara_symbol_gap(name: &str) -> Option<String> {
    (name.contains('|') || name.contains('\\')).then(|| {
        format!(
            "symbol `{name}` has no lossless standard quoted spelling in pinned Carcara \
             (it contains `|` or `\\`, which only the AY/Z3 escape extension can spell)"
        )
    })
}

/// Why one sort is outside pinned Carcara's sort grammar, if it is: the
/// innermost offending sort or symbol is named, so an `(Array Int (Seq Int))`
/// reports the `Seq`.
fn carcara_sort_gap(sort: &Sort) -> Option<String> {
    match sort {
        Sort::FloatingPoint(..) | Sort::Seq(_) | Sort::Char => Some(format!(
            "sort {} is not in pinned Carcara 1.1.0's sort grammar \
             (it has no FloatingPoint, Seq or Char sort)",
            format_sort_alethe(sort)
        )),
        Sort::Array(array) => {
            carcara_sort_gap(&array.index_sort).or_else(|| carcara_sort_gap(&array.element_sort))
        }
        Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => {
            carcara_symbol_gap(name)
        }
        Sort::Datatype(datatype) => carcara_symbol_gap(&datatype.name).or_else(|| {
            datatype.constructors.iter().find_map(|constructor| {
                carcara_symbol_gap(&constructor.name).or_else(|| {
                    constructor.fields.iter().find_map(|field| {
                        carcara_symbol_gap(&field.name).or_else(|| carcara_sort_gap(&field.sort))
                    })
                })
            })
        }),
        Sort::Bool | Sort::Int | Sort::Real | Sort::BitVec(_) | Sort::String | Sort::RegLan => None,
        _ => Some(format!(
            "sort {} has no pinned-Carcara spelling",
            format_sort_alethe(sort)
        )),
    }
}

/// The external-recheck surface verdict of a proof: whether the pinned
/// Carcara checker (1.1.0) can parse every sort and symbol spelling the
/// rendered Alethe document contains.
///
/// This is a DISCLOSURE carried by the artifact, not a gate on rendering
/// (owner decision D7, 2026-09-22). The printer renders what AY's strict
/// checker accepted for every sort; a consumer that CLAIMS an external Carcara
/// check — `--strict-proofs`, `--self-check`, a Carcara cross-check — refuses
/// an `Unsupported` document with its reason, fail-closed where the claim is
/// made, and a consumer that claims none takes the document at the
/// strict-checker class and never promotes it past that.
///
/// `#[non_exhaustive]`: a consumer must treat any variant it does not know as
/// unsupported, never as checked.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CarcaraSurface {
    /// Every sort and symbol spelling is in pinned Carcara's grammar, so the
    /// document can be handed to it as-is, and no step is spelled for one of
    /// its invocations only ([`Self::WithoutLetExpansion`]): the spelling
    /// reads the same with or without `--expand-let-bindings`.
    ///
    /// A claim about spellings, not that every step checks: a disclosed
    /// `hole`, or a premise `assume` that is not the problem's own — such as
    /// one that matches a `let` premise only after expansion, which only
    /// `--expand-let-bindings` accepts — is reported beside this verdict
    /// (the CLI's `unproved_steps` and `foreign_assumes`).
    Supported,
    /// Pinned Carcara cannot parse the document; `reason` names the first
    /// sort or symbol spelling outside its grammar (`Seq`, `FloatingPoint` and
    /// `Char` sorts, and symbols that need the AY/Z3 `\|`/`\\` escape
    /// extension). AY's own strict checker is unaffected by this verdict.
    Unsupported {
        /// Stable, human-readable cause, suitable for a refusal message.
        reason: String,
    },
    /// Pinned Carcara parses the document but refuses a step in it: the
    /// render kept `spelling`, which only Clean's vendored Carcara (the
    /// checker external-codegen promotes on) accepts. See `crate::AletheDialect`.
    /// Only a document that is otherwise [`Self::Supported`] says this; the
    /// CLI's certificate line says `carcara_surface=clean-dialect`.
    CleanDialect {
        /// The first Clean-only spelling the render kept.
        spelling: crate::CleanOnlySpelling,
    },
    /// Pinned Carcara checks the document only when it is run WITHOUT
    /// `--expand-let-bindings` (`carcara check -- PROOF PROBLEM`, AY's
    /// canonical invocation): the render eliminated a `let` the problem wrote
    /// with `:rule let`, and that flag expands the `let` at parse time, before
    /// the rule sees it. No spelling is valid in both invocations (see
    /// `crate::AletheDialectReport::eliminates_problem_let`). Only a document
    /// that is otherwise [`Self::Supported`] says this; the CLI's certificate
    /// line says `carcara_surface=without-let-expansion`.
    WithoutLetExpansion,
}

impl CarcaraSurface {
    /// Whether the document can be handed to pinned Carcara as-is.
    #[must_use]
    pub fn is_supported(&self) -> bool {
        matches!(self, Self::Supported)
    }

    /// The disclosed reason when the surface is not [`Self::Supported`]: the
    /// sort or symbol pinned Carcara cannot parse, the Clean-only spelling it
    /// refuses, or the invocation it must be run in.
    #[must_use]
    pub fn unsupported_reason(&self) -> Option<&str> {
        match self {
            Self::Supported => None,
            Self::Unsupported { reason } => Some(reason),
            Self::CleanDialect { spelling } => Some(spelling.describe()),
            Self::WithoutLetExpansion => Some(
                "the document eliminates the problem's own `let` with `:rule let`, which pinned \
                 Carcara checks only without `--expand-let-bindings`",
            ),
        }
    }
}

impl std::fmt::Display for CarcaraSurface {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Supported => f.write_str("supported"),
            Self::Unsupported { reason } => write!(f, "unsupported({reason})"),
            Self::CleanDialect { spelling } => write!(f, "clean-dialect({})", spelling.describe()),
            Self::WithoutLetExpansion => f.write_str("without-let-expansion"),
        }
    }
}

/// The first gap of each class found by one walk over a proof.
///
/// The two classes have different readers. A STRUCTURAL gap — a term handle
/// outside the store, a malformed `nra_sos` payload, a step kind with no
/// rendering — means the printer cannot render the document at all and keeps
/// refusing it. A DIALECT gap means the document renders but pinned Carcara
/// cannot parse it; that is disclosed, never refused, so the walk records the
/// first of each rather than stopping at the first of either.
#[derive(Default)]
struct CarcaraSurfaceScan {
    structural: Option<&'static str>,
    dialect: Option<String>,
}

impl CarcaraSurfaceScan {
    fn structural(&mut self, reason: &'static str) {
        self.structural.get_or_insert(reason);
    }

    fn dialect(&mut self, gap: Option<String>) {
        if self.dialect.is_none() {
            self.dialect = gap;
        }
    }
}

fn carcara_surface_scan(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> CarcaraSurfaceScan {
    let mut scan = CarcaraSurfaceScan::default();
    if let Some(overrides) = term_overrides {
        // The smallest offending spelling, so the disclosed reason does not
        // depend on the table's iteration order.
        let offending = overrides
            .values()
            .filter(|surface| {
                !crate::la_generic_signs::carcara_quoted_symbols_are_lexically_supported(surface)
            })
            .min();
        scan.dialect(offending.map(|surface| {
            const SHOWN: usize = 96;
            let shown: String = surface.chars().take(SHOWN).collect();
            let ellipsis = if surface.chars().count() > SHOWN {
                "…"
            } else {
                ""
            };
            format!(
                "authored spelling `{shown}{ellipsis}` quotes a symbol with the AY/Z3 \
                 `\\|`/`\\\\` escape extension, which pinned Carcara rejects"
            )
        }));
    }

    let mut stack = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => stack.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                stack.extend(clause.iter().copied());
                stack.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } | ProofStep::FiniteFieldLinear { clause, .. } => {
                stack.extend(clause.iter().copied())
            }
            ProofStep::NraSos {
                clause,
                certificate,
            } => {
                if clause.len() > ay_core::NraSosCertificate::MAX_CLAUSE_SLOTS
                    || certificate.validate_shape().is_err()
                    || clause
                        .iter()
                        .chain(certificate.basis.iter().flatten())
                        .any(|term| term.index() >= terms.len())
                {
                    scan.structural(
                        "an nra_sos step carries a malformed certificate or a term handle \
                         outside the term store",
                    );
                    continue;
                }
                stack.extend(clause.iter().copied());
                stack.extend(certificate.basis.iter().flatten().copied());
            }
            ProofStep::Step { clause, args, .. } => {
                stack.extend(clause.iter().copied());
                stack.extend(args.iter().copied());
            }
            ProofStep::Anchor { variables, .. } => {
                scan.dialect(variables.iter().find_map(|(name, sort)| {
                    carcara_symbol_gap(name).or_else(|| carcara_sort_gap(sort))
                }));
            }
            _ => scan.structural("a proof step has a kind with no Alethe rendering"),
        }
    }

    let mut visited = HashSet::default();
    while let Some(term) = stack.pop() {
        // A live root need not have live descendants in an untrusted restored
        // store. Refuse each missing handle before sort/content lookup.
        if term.index() >= terms.len() {
            scan.structural("the proof references a term handle outside the term store");
            continue;
        }
        if !visited.insert(term) {
            continue;
        }
        scan.dialect(carcara_term_gap(terms, term));
        stack.extend(terms.children(term));
    }
    scan
}

/// The first dialect gap in one LIVE term's own sort and spelling (its
/// children are walked by the caller).
fn carcara_term_gap(terms: &TermStore, term: TermId) -> Option<String> {
    carcara_sort_gap(terms.sort(term)).or_else(|| match terms.get(term) {
        TermData::Var(name, _) => carcara_symbol_gap(name),
        TermData::App(symbol, _) => carcara_symbol_gap(symbol.name()),
        TermData::Let(bindings, _) => bindings
            .iter()
            .find_map(|(name, _)| carcara_symbol_gap(name)),
        TermData::Forall(variables, _, _) | TermData::Exists(variables, _, _) => variables
            .iter()
            .find_map(|(name, sort)| carcara_symbol_gap(name).or_else(|| carcara_sort_gap(sort))),
        _ => None,
    })
}

/// The PARSE half of the external-recheck surface verdict of `proof` with
/// `term_overrides` (see [`CarcaraSurface`]): only ever
/// [`CarcaraSurface::Supported`] or [`CarcaraSurface::Unsupported`]. What a
/// render prints — a spelling only Clean's vendored Carcara checks, a
/// `:rule let` over the problem's own `let` — is decided at render time, so
/// `Supported` here is not a verdict on a rendered document (it reads
/// `Supported` for the UMULL `zero_extend` twin whose document pinned
/// Carcara 9a352ee refuses). Fold in the report
/// [`crate::capture_alethe_dialect_report`] returns around that render with
/// [`CarcaraSurface::with_dialect_report`].
///
/// Carcara does not parse AY's `Seq`, `FloatingPoint`, or `Char` sorts, and it
/// follows standard quoted-symbol syntax rather than Z3's `\|`/`\\` escape
/// extension. A proof containing either class renders — the strict checker's
/// verdict on it is unchanged — and is disclosed here as `Unsupported` with
/// the first offender named, so that only a consumer claiming an external
/// check refuses it. A proof the printer cannot render at all (a term handle
/// outside the store, a malformed `nra_sos` payload) is `Unsupported` too,
/// with that structural cause.
#[must_use]
pub fn carcara_proof_surface(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> CarcaraSurface {
    let scan = carcara_surface_scan(proof, terms, term_overrides);
    match scan.structural.map(str::to_string).or(scan.dialect) {
        None => CarcaraSurface::Supported,
        Some(reason) => CarcaraSurface::Unsupported { reason },
    }
}

/// Whether every proof term has a lossless spelling in the pinned Carcara
/// parser's sort and symbol grammar: [`carcara_proof_surface`] as a predicate.
///
/// This is the deciding predicate of the consumers that CLAIM an external
/// check (`Executor::unsat_proof_references_uncheckable_seq_theory`, the
/// known-wire-gap publication screen); it is no longer a rendering gate.
#[must_use]
pub fn carcara_proof_surface_is_supported(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    carcara_proof_surface(proof, terms, term_overrides).is_supported()
}

/// The structural gap that stops the printer rendering `proof` at all, if
/// any. Dialect gaps (sorts and spellings pinned Carcara cannot parse) are not
/// reported here: they render and are disclosed by [`carcara_proof_surface`].
pub(crate) fn carcara_structural_gap(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
) -> Option<&'static str> {
    carcara_surface_scan(proof, terms, term_overrides).structural
}

/// Whether the rendered equalities still form the exact non-redundant path
/// certified for a generic transitivity step.
///
/// Carcara consumes the printed endpoints, while AY's strict checker consumes
/// the internal term DAG. A document-wide authored override can change that
/// graph without changing the checked terms, so the renderer and terminal
/// policy both rebuild the bounded path from the effective wire spelling and
/// fail closed on a disconnected or redundant premise.
#[must_use]
pub fn trans_step_surface_is_supported(
    terms: &TermStore,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> bool {
    const MAX_TRANS_PREMISES: usize = 1_024;
    const MAX_TRANS_SURFACE_WORK: u64 = 1024 * 1024;
    if !(2..=MAX_TRANS_PREMISES).contains(&premise_clauses.len()) {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        term_overrides,
        Some(MAX_TRANS_SURFACE_WORK),
    );
    let decode = |clause: &[TermId]| -> Option<(String, String)> {
        let [literal] = clause else {
            return None;
        };
        let rendered = printer.format_term(*literal);
        if printer.work_used() > MAX_TRANS_SURFACE_WORK {
            return None;
        }
        let endpoints =
            split_alethe_application_bounded(&rendered, "=", 2, MAX_TRANS_SURFACE_WORK as usize)
                .ok()?;
        let [left, right] = endpoints.as_slice() else {
            return None;
        };
        Some(((*left).to_string(), (*right).to_string()))
    };
    let Some((goal_left, goal_right)) = decode(clause) else {
        return false;
    };
    let Some(edges) = premise_clauses
        .iter()
        .map(|premise| decode(premise))
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };

    let mut adjacency: HashMap<String, Vec<(String, usize)>> = HashMap::default();
    for (index, (left, right)) in edges.iter().enumerate() {
        adjacency
            .entry(left.clone())
            .or_default()
            .push((right.clone(), index));
        adjacency
            .entry(right.clone())
            .or_default()
            .push((left.clone(), index));
    }
    let mut parent: HashMap<String, (String, usize)> = HashMap::default();
    parent.insert(goal_left.clone(), (goal_left.clone(), usize::MAX));
    let mut frontier = std::collections::VecDeque::from([goal_left.clone()]);
    while let Some(current) = frontier.pop_front() {
        if current == goal_right {
            break;
        }
        if let Some(neighbors) = adjacency.get(&current) {
            for (next, edge) in neighbors {
                if !parent.contains_key(next) {
                    parent.insert(next.clone(), (current.clone(), *edge));
                    frontier.push_back(next.clone());
                }
            }
        }
    }
    if !parent.contains_key(&goal_right) {
        return false;
    }
    let mut path_length = 0usize;
    let mut current = goal_right;
    while current != goal_left {
        let Some((previous, _)) = parent.get(&current) else {
            return false;
        };
        path_length += 1;
        current = previous.clone();
    }
    path_length == edges.len()
}

/// Nesting cap for the printed-body skeleton comparison.
const MAX_SURFACE_SKELETON_DEPTH: usize = 256;

/// The connectives whose SHAPE a printed proof's rules read: `and_pos` and
/// `and_neg` index the operands of an `and`, `or_pos` compares an `or`'s
/// arity against the clause tail, `implies_pos` / `not_not` / `equiv_pos`
/// project through `=>`, `not` and `=`, and `ite_pos` through `ite`.
///
/// Everything else is a theory atom: one opaque leaf to every one of those
/// rules, and the place the term store's normalisation lives.
fn is_structural_connective(symbol: &str) -> bool {
    matches!(symbol, "and" | "or" | "not" | "=>" | "xor" | "ite" | "=")
}

/// The atom-head normalisations the term store performs at CONSTRUCTION and
/// that a carried authored body may therefore spell differently from the
/// store: `mk_gt` builds `(< b a)` for `(> a b)` and `mk_ge` builds `(<= b
/// a)` for `(>= a b)` (`arith_div_cmp.rs`). The `and_pos` bridge derives the
/// store's operand from the authored one across exactly these
/// (`printed_la_generic_unit_implication_is_supported`; MEASURED `valid` on
/// `greenflag13`, whose `(>= z 0)` is `(<= 0 z_3)` to the store). Nothing
/// else is enumerated: a spelling this list does not name falls back to the
/// store's own, which is what the base prints — an honest hole, never a
/// refused export. A connective is never one.
fn store_normalised_atom_head(printed: &str, stored: &str) -> bool {
    matches!((printed, stored), (">", "<") | (">=", "<="))
}

/// The immediate fields of one printed application `(head a1 .. an)`,
/// `None` for an atom or for text that is not one balanced application.
fn printed_application_fields(printed: &str) -> Option<Vec<&str>> {
    let inner = printed
        .trim()
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))?;
    let fields = split_smt_term_slices_bounded(inner, usize::MAX, usize::MAX).ok()?;
    (!fields.is_empty()).then_some(fields)
}

/// Split a rendered application string `(op A1 ... An)` into its top-level
/// argument strings by balanced-token scanning. Returns `None` when `s` is
/// not an application of `op`.
fn split_application(s: &str, op: &str) -> Option<Vec<String>> {
    split_alethe_application_bounded(s, op, usize::MAX, usize::MAX)
        .ok()
        .map(|arguments| arguments.into_iter().map(str::to_string).collect())
}

/// The printed `(= b a)` for the printed binary equality `(= a b)`, or `None`
/// for anything that is not one.
///
/// Read off the PRINTED TEXT, never the term store: the divergence this serves
/// is precisely a term whose two occurrences print differently, so a
/// term-identity comparison is blind to it by construction.
fn printed_equality_flip(literal: &str) -> Option<String> {
    let operands = split_application(literal, "=")?;
    let [left, right] = operands.as_slice() else {
        return None;
    };
    Some(format!("(= {right} {left})"))
}

/// Pair each printed leaf of an `or_pos` gate with the traced clause literal it
/// has to become, admitting exactly ONE kind of difference: a leaf and its
/// traced literal that are the two printed orientations of one equality.
///
/// WHY THIS EXISTS. The surface-override ledger maps a TERM to a spelling, and
/// a COMPOSITE entry carries its own spelling of every subterm. When the entry
/// for an `(or ...)` survives and the entry for one of its operands does not,
/// that operand prints one way inside the gate and the other way as a clause
/// literal — one term, two spellings, in one step. Measured on QF_UF
/// `iso_icl1206`: the gate's third leaf prints `(= (op e2 (op e2 e2)) e2)` and
/// the traced literal for the same `TermId` prints `(= e2 (op e2 (op e2 e2)))`.
///
/// Returns the per-leaf target spellings (what the re-derived step must
/// conclude) and the leaves that need a bridge. `None` — and therefore the
/// caller's decline — for any other difference: this must never invent a
/// pairing, only recognise the one the checker's own `eq_symmetric` rule
/// justifies.
#[expect(
    clippy::type_complexity,
    reason = "the return pair exposes exact per-leaf targets and explicit bridge pairs"
)]
fn match_printed_leaves_to_tail(
    leaves: &[String],
    tail: &[String],
) -> Option<(Vec<String>, Vec<(String, String)>)> {
    let mut unclaimed: Vec<Option<&str>> = tail.iter().map(|t| Some(t.as_str())).collect();
    let mut targets: Vec<Option<String>> = vec![None; leaves.len()];
    // Exact matches first, so a leaf that is literally present can never
    // consume the flip partner another leaf needs.
    for (index, leaf) in leaves.iter().enumerate() {
        if let Some(slot) = unclaimed.iter().position(|t| *t == Some(leaf.as_str())) {
            unclaimed[slot] = None;
            targets[index] = Some(leaf.clone());
        }
    }
    let mut bridges = Vec::new();
    for (index, leaf) in leaves.iter().enumerate() {
        if targets[index].is_some() {
            continue;
        }
        let flipped = printed_equality_flip(leaf)?;
        let slot = unclaimed
            .iter()
            .position(|t| *t == Some(flipped.as_str()))?;
        unclaimed[slot] = None;
        bridges.push((leaf.clone(), flipped.clone()));
        targets[index] = Some(flipped);
    }
    // Every traced literal must be reached, or the re-derived step concludes
    // a clause the document's consumers do not cite.
    if unclaimed.iter().any(Option::is_some) {
        return None;
    }
    targets
        .into_iter()
        .collect::<Option<Vec<String>>>()
        .map(|targets| (targets, bridges))
}

/// Split the *body* of an s-expression into its top-level tokens by balanced
/// scanning. `inner` is everything between the outermost parentheses; unlike
/// [`split_application`] no leading operator is stripped, so this also serves
/// binding lists (`(?v_0 e0) (?v_1 e1)`). Returns `None` on unbalanced input.
fn split_sexpr_tokens(inner: &str) -> Option<Vec<String>> {
    split_smt_terms(inner)
}

/// Split a printed application whose head is an SMT-LIB INDEXED identifier
/// into that head and its arguments: `((_ extract 1 0) x)` becomes
/// `("(_ extract 1 0)", ["x"])`.
///
/// `None` for anything else, including an ordinary application — the caller is
/// a repair for the one printed shape the pinned external checker's congruence
/// rules refuse, and must not reshape any other step.
fn split_printed_indexed_application(s: &str) -> Option<(String, Vec<String>)> {
    let inner = s.strip_prefix('(')?.strip_suffix(')')?;
    let mut tokens = split_sexpr_tokens(inner)?;
    if tokens.len() < 2 {
        return None;
    }
    let head = tokens.remove(0);
    // An indexed identifier is `(_ name i1 .. ik)`; nothing else qualifies.
    let head_inner = head.strip_prefix('(')?.strip_suffix(')')?;
    let head_tokens = split_sexpr_tokens(head_inner)?;
    if head_tokens.first().map(String::as_str) != Some("_") || head_tokens.len() < 2 {
        return None;
    }
    Some((head, tokens))
}

/// A decoded bit-wise-idempotent bit-vector gate: the SMT-LIB operator, the
/// Carcara bit-blasting rule for it, the Boolean connective that rule builds
/// each bit from, the simplification rule discharging that connective's
/// idempotency, and the repeated operand.
type IdempotentBvGate<'n> = (&'n str, &'n str, &'n str, &'n str, TermId);

/// One `let` level of a printed surface term: its bindings and its body.
type PrintedLetLevel = (Vec<(String, String)>, String);

/// Parse a printed `(let ((v1 e1) .. (vk ek)) BODY)` into its bindings and
/// body. Purely textual: the argument is the PROBLEM'S SURFACE SPELLING as
/// recorded in `term_overrides`, so there is no term to consult.
fn split_printed_let(s: &str) -> Option<PrintedLetLevel> {
    let inner = s
        .strip_prefix('(')?
        .strip_prefix("let")?
        .strip_suffix(')')?;
    // An opening parenthesis is an SMT-LIB token delimiter, so the compact
    // spelling `(let((x true))x)` is just as lexical as the spaced form.  The
    // binding-list and body checks below still require the exact `let` grammar.
    if !inner.starts_with('(') && !inner.starts_with(|c: char| c.is_ascii_whitespace()) {
        return None;
    }
    let mut tokens = split_sexpr_tokens(inner)?;
    if tokens.len() != 2 {
        return None;
    }
    let body = tokens.pop()?;
    let binding_list = tokens.pop()?;
    let binding_inner = binding_list.strip_prefix('(')?.strip_suffix(')')?;
    let mut bindings = Vec::new();
    for binding in split_sexpr_tokens(binding_inner)? {
        let pair_inner = binding.strip_prefix('(')?.strip_suffix(')')?;
        let mut pair = split_sexpr_tokens(pair_inner)?;
        if pair.len() != 2 {
            return None;
        }
        let value = pair.pop()?;
        let name = pair.pop()?;
        // A bound name must be an atom; `((a b) e)` is not a `let` binding.
        if name.starts_with('(') {
            return None;
        }
        bindings.push((name, value));
    }
    if bindings.is_empty() {
        return None;
    }
    Some((bindings, body))
}

/// Peel every nested `let` level off a printed term, outermost first.
///
/// Returns the levels and the innermost (still `?v`-bearing) body. `None` when
/// `s` is not a `let`.
fn peel_printed_lets(s: &str) -> Option<(Vec<PrintedLetLevel>, String)> {
    let mut levels = Vec::new();
    let mut current = s.to_string();
    while let Some((bindings, body)) = split_printed_let(&current) {
        levels.push((bindings, body.clone()));
        current = body;
        // Pathological nesting is a printing bug, not a proof; bail out rather
        // than build an unbounded anchor stack.
        if levels.len() > 64 {
            return None;
        }
    }
    if levels.is_empty() {
        None
    } else {
        Some((levels, current))
    }
}

/// Fully expanded view of a PRINTED `and`/`or` nesting.
///
/// THE SHARED PRINTED-SHAPE HELPER for both `and_pos` and `or_pos`. AY's
/// `mk_and`/`mk_or` flatten (`ay-core/src/term/boolean.rs`), so the INTERNAL
/// operand vector is n-ary; a surface override re-spells the same term with the
/// problem file's binary nesting. Both gate rules then break, in mirror-image
/// ways:
///
/// * `and_pos` compares `conclusion[1]` against `and_contents[args[0]]` with a
///   SYNTACTIC `assert_eq`, so an internal index has no meaning against a
///   printed shape of different arity;
/// * `or_pos` requires the gate's TOP-LEVEL arity to equal the clause tail
///   length — "expected 6 terms in 'or' term, got 2" for a printed
///   `(or (or (or (or (or (= x 0) (= x 1)) (= x 2)) ..)))`.
///
/// Rather than re-spell the term (which would desynchronize the `assume` that
/// still has to match the problem premise), walk the printed nesting and emit
/// one genuine gate step per printed node. Every consecutive `(parent, child)`
/// pair is a real `and_pos`/`or_pos` instance at the recorded operand index, so
/// the chain is checkable without changing a single printed TERM.
#[derive(Default)]
struct PrintedNesting {
    /// Printed spelling of each node; node 0 is the root.
    nodes: Vec<String>,
    /// Top-level printed operands of each node.
    operands: Vec<Vec<String>>,
    /// `(parent node, operand index within the parent)`; `None` for the root.
    parent: Vec<Option<(usize, usize)>>,
    /// Operands that are NOT themselves `op` applications, in printed
    /// left-to-right order — i.e. the flattened disjunct/conjunct list.
    leaves: Vec<String>,
}

impl PrintedNesting {
    /// Expand the printed `op`-nesting rooted at `root`.
    ///
    /// `None` when `root` is not an `op` application or the walk exceeds
    /// `node_budget` nodes / a fixed depth cap — the caller must then fail
    /// loud rather than emit an unverifiable gate.
    fn build(root: &str, op: &str, node_budget: usize) -> Option<Self> {
        let mut nesting = Self::default();
        nesting.push_node(root.to_string(), None);
        nesting.expand(0, op, node_budget, 0)?;
        Some(nesting)
    }

    fn push_node(&mut self, node: String, parent: Option<(usize, usize)>) -> usize {
        self.nodes.push(node);
        self.operands.push(Vec::new());
        self.parent.push(parent);
        self.nodes.len() - 1
    }

    fn expand(&mut self, node: usize, op: &str, node_budget: usize, depth: usize) -> Option<()> {
        if depth > 1024 {
            return None;
        }
        let operands = split_application(&self.nodes[node], op)?;
        self.operands[node] = operands.clone();
        for (index, operand) in operands.iter().enumerate() {
            if split_application(operand, op).is_some() {
                if self.nodes.len() >= node_budget {
                    return None;
                }
                let child = self.push_node(operand.clone(), Some((node, index)));
                self.expand(child, op, node_budget, depth + 1)?;
            } else {
                self.leaves.push(operand.clone());
            }
        }
        Some(())
    }

    /// `true` when the printed root is already flat — nothing to navigate.
    fn is_flat(&self) -> bool {
        self.nodes.len() == 1
    }

    /// The chain of `(node, operand index)` hops from the root down to `node`,
    /// outermost first.
    fn path_to(&self, node: usize) -> Vec<(usize, usize)> {
        let mut path = Vec::new();
        let mut current = node;
        while let Some((parent, index)) = self.parent[current] {
            path.push((parent, index));
            current = parent;
        }
        path.reverse();
        path
    }

    /// The shallowest node with `wanted` among its top-level operands.
    fn find_operand(&self, wanted: &str) -> Option<(usize, usize)> {
        let mut best: Option<(usize, usize, usize)> = None;
        for (node, operands) in self.operands.iter().enumerate() {
            let Some(index) = operands.iter().position(|o| o == wanted) else {
                continue;
            };
            let depth = self.path_to(node).len();
            if best.is_none_or(|(_, _, best_depth)| depth < best_depth) {
                best = Some((node, index, depth));
            }
        }
        best.map(|(node, index, _)| (node, index))
    }
}

// NOTE ON THE ROAD NOT TAKEN. Instead of navigating the printed nesting, the
// printed spine could be FLATTENED (`(and (and a b) c)` -> `(and a b c)`), which
// carcara's `assume` matching does accept: `Polyeq::mod_nary` collapses
// left-associated spines at any depth (`compare_assoc`, `Operator::And | Or =>
// NaryCase::LeftAssoc`), even through a `let` binder. It was rejected because it
// only works if the ASSUME is re-spelled too — and re-spelling a premise that
// currently matches, for every assertion in the corpus, is a far wider blast
// radius than emitting extra steps. It is also only sound for a LEFT spine:
// measured, `(and p (and q r))` -> `(and p q r)` and
// `(and (and p (and q r)) s)` -> `(and p q r s)` are both REJECTED as
// "could not match term to any of the original problem premises". The navigator
// above changes no printed term at all.

fn format_rational64(r: &num_rational::Rational64) -> String {
    let mut numer = *r.numer();
    let mut denom = *r.denom();
    if denom < 0 {
        numer = -numer;
        denom = -denom;
    }
    if denom == 1 {
        numer.to_string()
    } else {
        // Carcara requires Real literals (/ 1.0 2.0) not (/ 1 2)
        format!("(/ {numer}.0 {denom}.0)")
    }
}
