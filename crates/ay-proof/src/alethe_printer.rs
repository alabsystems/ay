// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe proof format printer.
//!
//! Formats proof steps, clauses, terms, and constants as SMT-LIB/Alethe text.

#[path = "alethe_printer_eq_transitive.rs"]
mod eq_transitive;
mod folded_assume;
#[cfg(test)]
#[path = "alethe_printer_ground_eval_tests.rs"]
mod ground_eval_tests;
#[path = "alethe_printer_resolution_args.rs"]
mod resolution_args;
#[path = "alethe_printer/store_permutation.rs"]
mod store_permutation;
mod surface_and_pos;
mod surface_symm;
mod surface_tokens;
mod term_format;
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
    /// [`AlethePrinter::skolem_choice_definitions`]. A symbol with no such
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
    /// Proof-local renderings introduced by certified Skolem expansion. These
    /// map the fresh witness to its Hilbert-choice term and propagate source
    /// surface syntax across the exact binder substitution.
    skolem_overrides: std::cell::RefCell<HashMap<TermId, String>>,
    /// Fresh witnesses rendered as `choice`, hence never free declarations.
    skolem_witness_names: std::cell::RefCell<HashSet<String>>,
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
    /// Subset of [`Self::folded_assume_surfaces`] whose `assume` is a PREMISE
    /// of some step, and therefore owes the consumers a derivation of the
    /// folded clause. An assumption nothing consumes owes nothing and is
    /// printed unchanged — introducing a bridge (and, in the worst case, a
    /// `hole`) for it would put an unproved step into a document that had none.
    folded_assume_bridged: std::cell::RefCell<HashSet<TermId>>,
    /// Internal clauses by proof id, populated eagerly so a resolution step
    /// can repair surface-order complements in its already-printed premises.
    proof_clauses: std::cell::RefCell<HashMap<ProofId, Vec<TermId>>>,
    /// Accumulated rendering work; see [`AlethePrintError::EmissionBudgetExhausted`].
    work: std::cell::Cell<u64>,
    /// Optional cap on `work` (#A2b, synthesized-default emission only).
    work_budget: Option<u64>,
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
            skolem_overrides: std::cell::RefCell::new(HashMap::default()),
            skolem_witness_names: std::cell::RefCell::new(HashSet::default()),
            format_cache: std::cell::RefCell::new(HashMap::default()),
            assume_terms: std::cell::RefCell::new(HashMap::default()),
            let_bridge_renderings: std::cell::RefCell::new(HashMap::default()),
            folded_assume_surfaces: std::cell::RefCell::new(HashMap::default()),
            folded_assume_bridged: std::cell::RefCell::new(HashSet::default()),
            proof_clauses: std::cell::RefCell::new(HashMap::default()),
            work: std::cell::Cell::new(0),
            work_budget,
        }
    }

    /// Prepare every certified Skolem mapping before any declaration or proof
    /// step is emitted. This is intentionally eager: arithmetic/theory steps
    /// may mention the witness before the `sko_forall` step's proof ID.
    pub(crate) fn prepare_proof(&self, proof: &Proof) -> Result<(), AlethePrintError> {
        {
            let mut clauses = self.proof_clauses.borrow_mut();
            clauses.clear();
            for (index, step) in proof.steps.iter().enumerate() {
                let id = ProofId(index as u32);
                let clause = match step {
                    ProofStep::Assume(term) => Some(vec![*term]),
                    ProofStep::Resolution { clause, .. }
                    | ProofStep::TheoryLemma { clause, .. }
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
        self.plan_folded_and_assumes(proof);
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
            let TermData::Forall(bindings, body, _) = self.terms.get(quantified) else {
                unreachable!("strict Skolem validation fixed the source shape")
            };
            let [(binder, binder_sort)] = bindings.as_slice() else {
                unreachable!("strict Skolem validation fixed the binder arity")
            };
            let [witness] = args.as_slice() else {
                unreachable!("strict Skolem validation fixed the witness arity")
            };

            let (binder_token, body_surface) =
                self.skolem_surface_binder_and_body(quantified, *body, binder);
            let choice = format!("(choice (({binder_token} {binder_sort})) (not {body_surface}))");
            let instance_surface = substitute_smt_symbol(&body_surface, &binder_token, &choice);

            self.insert_skolem_override(id, *witness, choice.clone())?;
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
            let TermData::Var(witness_name, _) = self.terms.get(*witness) else {
                unreachable!("strict Skolem validation fixed witness shape")
            };
            self.skolem_witness_names
                .borrow_mut()
                .insert(witness_name.clone());
        }
        self.prepare_array_extensionality_choices(proof);
        // Preparation may have formatted source terms before their substituted
        // overrides were installed. Never retain a stale rendering.
        self.format_cache.borrow_mut().clear();
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
        let sort = self.terms.sort(witness);
        let binder = EXT_CHOICE_BINDER;
        format!(
            "(choice (({binder} {sort})) \
             (or (= {a} {b}) (not (= (select {a} {binder}) (select {b} {binder})))))"
        )
    }

    /// Select the binder token and body spelling used by every command in one
    /// expanded `sko_forall`.  A whole-quantifier surface override is the
    /// authority when present: using the internal body beside an authored
    /// `(=> ...)` quantifier produces an invalid mixed-identity anchor.
    fn skolem_surface_binder_and_body(
        &self,
        quantified: TermId,
        body: TermId,
        internal_binder: &str,
    ) -> (String, String) {
        if let Some(surface) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&quantified))
        {
            if let Some((binder, body)) = split_single_binder_quantifier(surface, "forall") {
                return (binder, body);
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
        // clause tail, or the emitted chain would not resolve to it.
        let mut sorted_leaves = nesting.leaves.clone();
        let mut sorted_tail = tail.clone();
        sorted_leaves.sort();
        sorted_tail.sort();
        if sorted_leaves != sorted_tail {
            return None;
        }
        let mut out = String::new();
        let mut premises = Vec::with_capacity(nesting.nodes.len());
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
        if premises.len() == 1 {
            // Single node: the chain degenerates to the spec step itself, so
            // emit it under the traced id instead of a resolution.
            return Some(format!(
                "(step {id} (cl (not {source_str}) {}) :rule or_pos)",
                nesting.leaves.join(" ")
            ));
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl (not {source_str}) {}) :rule resolution :premises ({}))",
                nesting.leaves.join(" "),
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
                let printed_arity = split_application(&self.format_term(source), "or")?.len();
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
    fn format_let_assume_bridge(&self, id: ProofId, term: TermId, surface: &str) -> Option<String> {
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
        let substituted = if printed_let_bindings_are_simple(&levels) {
            expand_printed_lets(&levels, &innermost_body)
        } else {
            String::new()
        };

        let mut out = String::new();
        let _ = std::fmt::Write::write_fmt(&mut out, format_args!("(assume {id}.a {surface})\n"));
        if substituted == eliminated {
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
                    "(step {refl_id} (cl (= {innermost_body} {substituted})) :rule refl)\n"
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
                        "(step {level_id} (cl (= {level_surface} {substituted})) :rule let)\n"
                    ),
                );
            }
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
    /// Return the actual accumulated rendering work.
    pub(crate) fn work_used(&self) -> u64 {
        self.work.get()
    }
    /// Whether accumulated work exceeds the configured budget.
    pub(crate) fn work_budget_exhausted(&self) -> bool {
        self.work_budget.is_some_and(|b| self.work.get() > b)
    }
    /// Typed exhaustion error for the caller's per-step check.
    pub(crate) fn work_budget_error(&self, steps_rendered: u32) -> AlethePrintError {
        AlethePrintError::EmissionBudgetExhausted {
            budget: self.work_budget.unwrap_or(0),
            steps_rendered,
        }
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
        match step {
            ProofStep::Assume(term_id) => {
                self.assume_terms.borrow_mut().insert(id, *term_id);
                if let Some(bridge) = self.format_folded_and_assume_bridge(id, *term_id) {
                    return Ok(bridge);
                }
                let term_str = self.format_term(*term_id);
                if let Some(bridge) = self.format_let_assume_bridge(id, *term_id, &term_str) {
                    return Ok(bridge);
                }
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
                ..
            } => self.format_theory_lemma(id, theory, clause, farkas.as_ref(), kind),
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
        let TermData::Forall(bindings, body, _) = self.terms.get(quantified) else {
            unreachable!("validated Skolem source")
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
        let (binder, body) = self.skolem_surface_binder_and_body(quantified, *body, binder);
        let quantified = self.format_term(quantified);
        let instance = self.format_term(instance);
        Ok(format!(
            "(anchor :step {id} :args ((:= ({binder} {binder_sort}) {choice})))\n\
             (step {id}.t1 (cl (= {body} {instance})) :rule refl)\n\
             (step {id} (cl (= {quantified} {instance})) :rule sko_forall)"
        ))
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
        if let Some((left, right)) =
            self.surface_order_resolution_pair(clause, pivot, clause1, clause2)
        {
            return Ok(format!(
                "(step {id}.ord (cl (not {left}) (not {right})) :rule la_generic :args (1 1))\n\
                 (step {id} {} :rule resolution :premises ({clause1} {id}.ord {clause2}))",
                self.format_clause(clause)
            ));
        }

        // Omit :args — Carcara infers an ordinary syntactic pivot from the
        // premises.
        Ok(format!(
            "(step {id} {} :rule resolution :premises ({clause1} {clause2}))",
            self.format_clause(clause)
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
        let mut expected: Vec<String> = clause.iter().map(|&l| self.format_term(l)).collect();
        expected.sort();

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
                if rest_sorted != expected {
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

    /// Render an independently evaluated ground LIA unit through the exact
    /// rules implemented by the pinned external checker.
    ///
    /// Carcara treats `lia_generic` as an unchecked hole. A positive
    /// directional equality can use `evaluate` directly. A true ground
    /// disequality cannot: `evaluate` only concludes `(= term value)`, so spell
    /// out the checked `evaluate` / `equiv1` / `false` / `resolution` bridge.
    ///
    /// The native ground evaluator is the authority here, independently of
    /// the LIA annotation. The canonical-surface equality is load-bearing: a
    /// source override that changes what the external checker sees must not
    /// inherit authority from the internal term DAG.
    fn format_lia_ground_evaluate(
        &self,
        id: ProofId,
        clause: &[TermId],
        clause_str: &str,
    ) -> Option<String> {
        if clause_str != AlethePrinter::new(self.terms).format_clause(clause) {
            return None;
        }
        if crate::checker::validate_ground_evaluate_for_printer(self.terms, id, clause, 0, &[])
            .is_ok()
        {
            return Some(format!("(step {id} {clause_str} :rule evaluate)"));
        }

        let [literal] = clause else {
            return None;
        };
        let TermData::Not(equality) = self.terms.get(*literal) else {
            return None;
        };
        let TermData::App(Symbol::Named(operator), operands) = self.terms.get(*equality) else {
            return None;
        };
        if operator != "="
            || operands.len() != 2
            || !crate::checker::recognize_ground_evaluate(self.terms, *literal)
        {
            return None;
        }

        let equality = self.format_term(*equality);
        let literal = self.format_term(*literal);
        Some(format!(
            "(step {id}.ev (cl (= {equality} false)) :rule evaluate)\n\
             (step {id}.q (cl {literal} false) :rule equiv1 :premises ({id}.ev))\n\
             (step {id}.f (cl (not false)) :rule false)\n\
             (step {id} {clause_str} :rule resolution :premises ({id}.q {id}.f))"
        ))
    }

    fn format_theory_lemma(
        &self,
        id: ProofId,
        theory: &str,
        clause: &[TermId],
        farkas: Option<&ay_core::FarkasAnnotation>,
        kind: &ay_core::TheoryLemmaKind,
    ) -> Result<String, AlethePrintError> {
        if matches!(kind, ay_core::TheoryLemmaKind::ArithEqTriangle) {
            return self.format_arith_eq_triangle(id, clause);
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArithEqImpliesBound) {
            return self.format_arith_eq_implies_bound(id, clause);
        }
        if matches!(kind, ay_core::TheoryLemmaKind::IntBoundsTautology) {
            return self.format_unit_farkas_clause(id, clause, "integer bounds tautology");
        }
        if matches!(kind, ay_core::TheoryLemmaKind::ArithDisequalitySplit) {
            return self.format_arith_disequality_split(id, clause);
        }
        // AY's wide BV checker proves binary `bvand` commutativity by building
        // and replaying a bit-blast/LRAT refutation from this exact live term.
        // Alethe has no monolithic `bv_bitblast` rule, but it does have the
        // independently checked `aci_simp` primitive for this same equality.
        // Lower only the exact printed operand-swap shape; every other internal
        // BvBitBlast lemma keeps the honest `hole` wire fallback below.
        if matches!(kind, ay_core::TheoryLemmaKind::BvBitBlast) {
            if let Some(text) = self.format_binary_bvand_aci_simp(id, clause) {
                return Ok(text);
            }
        }
        // The two bit-vector lemma families whose clauses are exactly
        // reconstructible from Carcara's own primitives. Both gates re-derive
        // the shape from the clause itself, so they are equally valid for the
        // gate-annotated kind, whose clause space is a SUBSET of the plain
        // one. Everything else keeps the honest `hole` fallback below.
        if matches!(
            kind,
            ay_core::TheoryLemmaKind::BvBitBlast | ay_core::TheoryLemmaKind::BvBitBlastGate { .. }
        ) {
            if let Some(text) = self.format_bv_constant_disequality(id, clause) {
                return Ok(text);
            }
            if let Some(text) = self.format_bv_idempotent_gate_bitblast(id, clause) {
                return Ok(text);
            }
            if let Some(text) = self.format_bv_double_negation_bitblast(id, clause) {
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
            if let Some(text) = self.format_array_row_chain(id, clause) {
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
        }

        let clause_str = self.format_clause(clause);
        if matches!(kind, ay_core::TheoryLemmaKind::LiaGeneric) {
            if let Some(text) = self.format_lia_ground_evaluate(id, clause, &clause_str) {
                return Ok(text);
            }
        }
        if let Some(farkas) = farkas {
            // WIRE name, not the internal one: a kind the checker does not
            // implement must print as `hole`, never as an unknown rule name
            // (which makes the whole document `invalid`). The arithmetic kinds
            // that actually reach here (`LraFarkas`, `LiaGeneric`) are
            // checkable and pass through unchanged.
            let rule = kind.alethe_wire_rule();
            // Alethe `la_generic` coefficients are SIGNED: an equality literal
            // used in the `rhs - lhs` orientation must print a negative
            // coefficient, while the internal certificate keeps non-negative
            // magnitudes and lets the validator search orientations. Resolve
            // the printed signs from the certificate's own contradicting
            // combination; certificates without equality literals (unique
            // orientations) come back bit-identical, and any conflict the
            // linear model cannot orient keeps the original coefficients.
            let printed_coefficients: Vec<num_rational::Rational64> = if rule == "la_generic" {
                let conflict: Vec<ay_core::TheoryLit> = clause
                    .iter()
                    .map(|&lit| match self.terms.get(lit) {
                        TermData::Not(inner) => ay_core::TheoryLit {
                            term: *inner,
                            value: true,
                        },
                        _ => ay_core::TheoryLit {
                            term: lit,
                            value: false,
                        },
                    })
                    .collect();
                {
                    // Sign the coefficients against the PRINTED atom orientation
                    // (what an external checker parses), not the internal term
                    // orientation — surface-syntax overrides can reorient an
                    // equality, flipping the sign the checker expects. Start
                    // from the internal orientation search, then repair the
                    // equality signs over the printed strings when needed
                    // (emission-only; kept byte-identical when already valid).
                    let existing = ay_core::proof_validation::resolve_equality_coefficient_signs(
                        self.terms, &conflict, farkas,
                    )
                    .unwrap_or_else(|| farkas.coefficients.clone());
                    let printed_atoms: Vec<(String, bool)> = conflict
                        .iter()
                        .map(|l| (self.format_term(l.term), l.value))
                        .collect();
                    crate::la_generic_signs::resolve_printed_la_generic_coefficients(
                        &printed_atoms,
                        &existing,
                        &farkas.coefficients,
                    )
                }
            } else {
                farkas.coefficients.clone()
            };
            let coeffs: Vec<String> = printed_coefficients.iter().map(format_rational64).collect();
            return Ok(format!(
                "(step {} {} :rule {} :args ({}))",
                id,
                clause_str,
                rule,
                coeffs.join(" ")
            ));
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

        // Non-arithmetic kinds fall through to their own rule name, mapped to
        // the WIRE name. Every lowering above this point that found a real
        // Alethe inference has already returned; what is left is a theory
        // lemma AY can state but not justify in the checker's calculus —
        // `TheoryLemmaKind::Generic` (internally `"trust"`), `dt_project`, the
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
        Ok(format!(
            "(step {id}.split (cl {packed}) :rule la_disequality)\n\
             (step {id} (cl {forward} {reverse} {equality}) :rule or :premises ({id}.split))"
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

    fn format_arith_disequality_split(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Result<String, AlethePrintError> {
        let [first, second, equality] = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "guarded arithmetic split must have three literals".to_string(),
            });
        };
        let TermData::App(Symbol::Named(eq_name), eq_args) = self.terms.get(*equality) else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "guarded arithmetic split must end in an equality".to_string(),
            });
        };
        if eq_name != "=" || eq_args.len() != 2 {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: "guarded arithmetic split must end in a binary equality".to_string(),
            });
        }
        let lhs = self.format_term(eq_args[0]);
        let rhs = self.format_term(eq_args[1]);
        let equality = self.format_term(*equality);
        let first = self.format_term(*first);
        let second = self.format_term(*second);
        let le_forward = format!("(<= {lhs} {rhs})");
        let le_reverse = format!("(<= {rhs} {lhs})");
        let packed = format!("(or {equality} (not {le_forward}) (not {le_reverse}))");
        Ok(format!(
            "(step {id}.split (cl {packed}) :rule la_disequality)\n\
             (step {id}.flat (cl {equality} (not {le_forward}) (not {le_reverse})) :rule or :premises ({id}.split))\n\
             (step {id}.b0 (cl {le_forward} {second}) :rule la_generic :args (1 1))\n\
             (step {id}.b1 (cl {le_reverse} {first}) :rule la_generic :args (1 1))\n\
             (step {id}.mid (cl {equality} (not {le_reverse}) {second}) :rule resolution :premises ({id}.flat {id}.b0))\n\
             (step {id} (cl {first} {second} {equality}) :rule resolution :premises ({id}.mid {id}.b1))"
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
        Some(format!(
            "(step {id} (cl (= {printed_left} {printed_right})) :rule aci_simp)"
        ))
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
                if printed_base != &base
                    || printed_store_index != &store_index
                    || printed_read_index != &read_index
                {
                    return Err(invalid_surface(format!(
                        "ROW1 select/store surface override changes the certified array or index: \
                             base={printed_base:?}/{base:?}, \
                             store_index={printed_store_index:?}/{store_index:?}, \
                             read_index={printed_read_index:?}/{read_index:?}"
                    )));
                }
                let needs_value_bridge = stored_value != &value;
                if needs_value_bridge {
                    let canonical_is_numeric = matches!(
                        self.terms.get(value_term),
                        TermData::Const(Constant::Int(_) | Constant::Rational(_))
                    );
                    let surface_values_match = canonical_is_numeric
                        && crate::la_generic_signs::parse_numeric_constant(stored_value)
                            .zip(crate::la_generic_signs::parse_numeric_constant(&value))
                            .is_some_and(|(stored, canonical)| stored == canonical);
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
                if printed_row != canonical_row && printed_row != reversed_row {
                    return Err(invalid_surface(
                        "ROW1 equality surface override is neither the certified orientation nor its symmetry"
                            .to_string(),
                    ));
                }

                let Some(guard) = guard else {
                    if !needs_value_bridge {
                        if printed_row == canonical_row {
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
                    if printed_row == canonical_row {
                        return Ok(format!(
                            "(step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                             (step {id}.val (cl (= {stored_value} {value})) :rule la_generic :args (1))\n\
                             (step {id} (cl {canonical_row}) :rule trans :premises ({id}.idx {id}.val))"
                        ));
                    }
                    return Ok(format!(
                        "(step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                         (step {id}.val (cl (= {stored_value} {value})) :rule la_generic :args (1))\n\
                         (step {id}.base (cl {canonical_row}) :rule trans :premises ({id}.idx {id}.val))\n\
                         (step {id} (cl {reversed_row}) :rule symm :premises ({id}.base))"
                    ));
                };

                let printed_guard = self.format_term(guard);
                let guard_forward = format!("(not (= {store_index} {read_index}))");
                let guard_reverse = format!("(not (= {read_index} {store_index}))");
                let assumed_equality = if printed_guard == guard_forward {
                    format!("(= {store_index} {read_index})")
                } else if printed_guard == guard_reverse {
                    format!("(= {read_index} {store_index})")
                } else {
                    return Err(invalid_surface(
                        "conditional ROW1 guard surface override changes the certified index pair"
                            .to_string(),
                    ));
                };
                let same_index_select = format!("(select {printed_store} {store_index})");
                let flat_id = packed_or.map_or_else(|| id.to_string(), |_| format!("{id}.flat"));
                let stored_row = format!("(= {same_index_select} {stored_value})");
                let (cong_row, cong_to_same) = if printed_guard == guard_forward {
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
                let cong_premise = if printed_guard == guard_forward {
                    format!("{id}.congs")
                } else {
                    format!("{id}.cong")
                };
                let mut output = format!(
                    "(anchor :step {flat_id})\n\
                     (assume {id}.h {assumed_equality})\n\
                     (step {id}.idx (cl {stored_row}) :rule arrays_idx)\n\
                     (step {id}.cong (cl {cong_row}) :rule cong :premises ({id}.h))"
                );
                if !cong_to_same.is_empty() {
                    output.push('\n');
                    output.push_str(&cong_to_same);
                }
                if needs_value_bridge {
                    let _ = std::fmt::Write::write_fmt(
                        &mut output,
                        format_args!(
                            "\n(step {id}.val (cl (= {stored_value} {value})) :rule la_generic :args (1))\n\
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
                if printed_row != canonical_row {
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
                value: _,
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
                if printed_base != &base
                    || printed_store_index != &store_index
                    || printed_store_read_index != &read_index
                    || printed_select_base_array != &base
                    || printed_base_read_index != &read_index
                {
                    return Err(invalid_surface(
                        "ROW2 select surface override changes the certified array or indices"
                            .to_string(),
                    ));
                }
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
                let reverse_final = if printed_conclusion == format!("(= {left_tail} {right_tail})")
                {
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
                if reverse_final {
                    body.push(format!(
                        "(step {id}.fin (cl {printed_conclusion}) :rule symm :premises ({}))",
                        if trans_premises.len() > 1 {
                            format!("{id}.tr")
                        } else {
                            format!("{id}.cong")
                        }
                    ));
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
                    {
                        return None;
                    }
                    // The strict checker certified this endpoint as the exact
                    // root read at `read_index`.  An authenticated enclosing
                    // select can nevertheless retain the source spelling
                    // `(+ read_index 0)`.  Keep that authored AST and bridge
                    // it explicitly: arithmetic proves the index identity,
                    // then congruence transports the read.  No surface string
                    // is treated as definitionally equal by the array rule.
                    let index_id = format!("{prefix}bi");
                    let select_id = format!("{prefix}bs");
                    lines.push(format!(
                        "(step {index_id} (cl (= {index_str} {tail_index})) :rule la_generic :args (1))"
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

    fn format_generic_step(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Result<String, AlethePrintError> {
        if matches!(rule, ay_core::AletheRule::Symm) {
            return self.format_surface_symm(id, clause, premises, args);
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
        if is_resolution {
            resolution_args::validate_generic_resolution_surface(self, clause, premises, args)
                .map_err(|reason| AlethePrintError::InvalidSurfaceStep { id, reason })?;
        }
        // A comparison may carry the authored `>=`/`>` spelling while its
        // canonical internal term is the equivalent argument-reversed
        // `<=`/`<` application. If that term is the left side of a `cong`
        // conclusion, the global override would otherwise make the printed
        // applications have different operators. Re-establish the canonical
        // application with `comp_simplify`, apply same-operator congruence,
        // then compose the equalities.
        if matches!(rule, ay_core::AletheRule::Cong) {
            if let Some(text) = self.surface_order_cong_bridge(id, clause, premises, args) {
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
            // misclassify that placeholder as malformed input.
            if matches!(rule, ay_core::AletheRule::AndPos(_)) && self.work_budget_exhausted() {
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
            if !matches!(rule, ay_core::AletheRule::AndPos(_)) {
                if let Some(text) = self.format_surface_tautology(id, rule, clause, args) {
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
            // FAIL LOUD for the two printed-shape defects this pass repairs.
            // Reaching here means every certified bridge declined, so the
            // DEFAULT rendering below is about to ship a step carcara rejects:
            //   * `and_pos` whose gate literal is the De Morgan or-form — the
            //     23-instance census class ("term '(or ..)' is of the wrong
            //     form, expected '(not(and ...))'");
            //   * `or_pos` whose printed gate arity differs from the clause
            //     tail ("expected 6 terms in 'or' term, got 2").
            // A wrong proof is worse than no proof: raise so the caller's
            // unverifiable-proof path fires instead.
            if let Some(reason) = self.unrepairable_gate_reason(rule, clause, args) {
                return Err(AlethePrintError::InvalidSurfaceStep { id, reason });
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
        let clause_str = self.format_clause(clause);
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
    /// equality, one matching unit-equality premise, exactly one differing
    /// application argument, and an exact argument-reversed order override on
    /// the conclusion's left side. Every other `cong` remains byte-unchanged.
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

        // Congruence is checked over the PRINTED premise too. Require it to be
        // exactly the equality between the one differing argument pair.
        let differing_left = self.format_term(differing_left);
        let differing_right = self.format_term(differing_right);
        let printed_premise = self.format_term(premise_literal);
        let premise_forward = format!("(= {differing_left} {differing_right})");
        let premise_reverse = format!("(= {differing_right} {differing_left})");
        if printed_premise != premise_forward && printed_premise != premise_reverse {
            return None;
        }

        let final_equality = format!("(= {printed_left} {printed_right})");
        if self.format_term(*conclusion) != final_equality {
            return None;
        }
        Some(format!(
            "(step {id}.norm (cl (= {printed_left} {canonical_left})) :rule comp_simplify)\n\
             (step {id}.cong (cl (= {canonical_left} {canonical_right})) :rule cong :premises ({premise}))\n\
             (step {id} (cl {final_equality}) :rule trans :premises ({id}.norm {id}.cong))"
        ))
    }

    /// Detect the externally invalid fallback the order-normalization bridge
    /// is meant to prevent. If the two printed applications use different
    /// comparison operators, a plain `cong` can never justify the equality.
    fn surface_cong_has_different_order_operators(&self, clause: &[TermId]) -> bool {
        let [conclusion] = clause else {
            return false;
        };
        let Some([left, right]) = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())
        else {
            return false;
        };
        matches!(
            (
                surface_order_operator(left.as_str()),
                surface_order_operator(right.as_str())
            ),
            (Some(left_op), Some(right_op)) if left_op != right_op
        )
    }

    /// Detect a printed `cong` conclusion that no congruence rule can check,
    /// returning the reason to DECLINE with.
    ///
    /// MEASURED against carcara 1.1.0 on a `(= x y)` premise, every shape below
    /// is rejected outright, so this can never withhold a step the checker
    /// would have accepted:
    ///
    /// | printed conclusion   | carcara                                        |
    /// |----------------------|------------------------------------------------|
    /// | `(= (g x) (f y))`    | `functions don't match: 'g' and 'f'`           |
    /// | `(= zzz (f y))`      | `term is not an application or operation: 'zzz'`|
    /// | `(= zzz x)`          | `term is not an application or operation: 'zzz'`|
    ///
    /// The bare-ATOM rows are why this does not simply compare head symbols:
    /// a sibling guard that required BOTH sides to be applications let
    /// `(= zzz (f y))` through to the default rendering, which shipped a step
    /// carcara rejects. An operand that is not a printed application fails the
    /// rule whatever the other side is, so it is reported here.
    ///
    /// `None` when the conclusion is not a printed binary `=`, when both heads
    /// agree, or when the rendering is not parseable as an application — those
    /// are left to the ordinary path rather than guessed at.
    fn surface_cong_has_uncheckable_operands(&self, clause: &[TermId]) -> Option<String> {
        let [conclusion] = clause else {
            return None;
        };
        let [left, right] = split_application(&self.format_term(*conclusion), "=")
            .and_then(|args| <[String; 2]>::try_from(args).ok())?;
        match (printed_head_symbol(&left), printed_head_symbol(&right)) {
            (Some(left_head), Some(right_head)) => {
                if left_head == right_head {
                    return None;
                }
                Some(format!(
                    "surface rewriting gives the two congruence applications different operators \
                     ('{left_head}' and '{right_head}')"
                ))
            }
            // Exactly one side is an application, or neither is. carcara needs
            // BOTH to be applications of the same operator.
            (None, Some(_)) | (Some(_), None) | (None, None) => Some(format!(
                "a congruence operand is not a printed application ('{left}' and '{right}'), \
                 which no congruence rule can check"
            )),
        }
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
                "surface left application no longer uses the certified operator {operator}"
            ));
        };
        let Some(right_args) = split_application(&printed_right, &operator) else {
            return Err(format!(
                "surface right application no longer uses the certified operator {operator}"
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

        let mut printed_clause: Vec<String> =
            clause.iter().map(|&term| self.format_term(term)).collect();
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
            if (hyp_left == expected_left && hyp_right == expected_right)
                || (hyp_left == expected_right && hyp_right == expected_left)
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
        let Some((index, original_hypothesis, hyp_left, hyp_right)) = mismatch else {
            return Ok(None);
        };
        if hyp_left != hyp_right {
            return Err(
                "surface eq_congruent mismatch is not the exact reflexive-hypothesis shape"
                    .to_string(),
            );
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

        let ac_equality = format!("(= {expected_left} {expected_right})");
        printed_clause[index] = format!("(not {ac_equality})");
        let corrected_clause = format!("(cl {})", printed_clause.join(" "));
        let original_clause = self.format_clause(clause);
        Ok(Some(format!(
            "(step {id}.ac (cl {ac_equality}) :rule aci_simp)\n\
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

    /// Resugar an `or` decomposition whose single assume premise is an
    /// internal canonical or-term but PRINTS as a right-associated binary
    /// implication chain.
    ///
    /// For `(=> A (=> B C))`, the internal `or` rule concludes
    /// `{(not A), (not B), C}` from the unit premise. The printed premise is
    /// not an or-term, so rebuild the same clause with stock Alethe rules:
    ///
    /// ```text
    /// imp0: (cl (not (=> A (=> B C))) (not A) (=> B C))  implies_pos
    /// imp1: (cl (not (=> B C)) (not B) C)                 implies_pos
    /// id:   (cl (not A) (not B) C)                        resolution premise,imp0,imp1
    /// ```
    ///
    /// This is deliberately narrower than semantic implication recognition.
    /// It fires only when all of these agree exactly as multisets and have the
    /// same arity: the internal or operands, the internal traced clause, the
    /// printed internal operands, and the literals obtained by flattening the
    /// printed right-associated implication. The n-ary resolution performs
    /// the same left-to-right pivot chain without quadratic intermediate
    /// clauses and retains the original id for every downstream reference.
    fn resugar_implies_decomposition(
        &self,
        id: ProofId,
        clause: &[TermId],
        premise: ProofId,
    ) -> Result<Option<String>, String> {
        let Some(&source) = self.assume_terms.borrow().get(&premise) else {
            return Ok(None);
        };
        let source_str = self.format_term(source);
        if split_binary_implies(&source_str).is_none() {
            if split_application(&source_str, "=>").is_some() {
                return Err("printed implication premise is not binary".to_string());
            }
            return Ok(None);
        }
        let TermData::App(Symbol::Named(name), source_disjuncts) = self.terms.get(source) else {
            return Err("printed implication premise is not an internal or-term".to_string());
        };
        if name != "or" || source_disjuncts.len() < 2 || source_disjuncts.len() != clause.len() {
            return Err("printed implication/internal or arity mismatch".to_string());
        }

        // Internal gate: the step must decompose this exact assumed or-term,
        // not merely a same-arity clause that happens to print similarly.
        let mut sorted_source = source_disjuncts.clone();
        let mut sorted_clause = clause.to_vec();
        sorted_source.sort_unstable();
        sorted_clause.sort_unstable();
        if sorted_source != sorted_clause {
            return Err(
                "or decomposition clause is not the assumed internal disjunct multiset".to_string(),
            );
        }

        let mut implication = source_str.clone();
        let mut links: Vec<(String, String, String)> = Vec::new();
        let mut flattened: Vec<String> = Vec::new();
        while let Some((antecedent, consequent)) = split_binary_implies(&implication) {
            if links.len() >= PRINTED_NESTING_NODE_BUDGET {
                return Err("printed implication nesting exceeds the printer limit".to_string());
            }
            flattened.push(format!("(not {antecedent})"));
            links.push((implication, antecedent, consequent.clone()));
            implication = consequent;
        }
        if links.is_empty() {
            return Ok(None);
        }
        // `split_binary_implies` also returns `None` for a non-binary `=>`.
        // Such a node is not an atomic final consequent of the admitted
        // right-nested binary chain; reject it explicitly instead of treating
        // the malformed implication application as a leaf.
        if split_application(&implication, "=>").is_some() {
            return Err("right-nested printed implication contains a non-binary link".to_string());
        }
        flattened.push(implication);
        if flattened.len() != source_disjuncts.len() {
            return Err("printed implication/internal or arity mismatch".to_string());
        }

        // Printed gate: surface overrides may change descendants as well as
        // the root. Require both the source operands and the traced clause to
        // be exactly the flattened implication literals, counting repeats.
        let mut printed_source: Vec<String> = source_disjuncts
            .iter()
            .map(|&literal| self.format_term(literal))
            .collect();
        let printed_clause: Vec<String> = clause
            .iter()
            .map(|&literal| self.format_term(literal))
            .collect();
        let mut sorted_printed_clause = printed_clause.clone();
        let mut sorted_flattened = flattened.clone();
        printed_source.sort_unstable();
        sorted_printed_clause.sort_unstable();
        sorted_flattened.sort_unstable();
        if printed_source != sorted_flattened || sorted_printed_clause != sorted_flattened {
            return Err(
                "printed implication literals do not match the internal source and conclusion"
                    .to_string(),
            );
        }

        let mut out = String::new();
        let mut resolution_premises = vec![premise.to_string()];
        for (index, (current, antecedent, consequent)) in links.iter().enumerate() {
            let implication_id = format!("{id}.imp{index}");
            let _ = std::fmt::Write::write_fmt(
                &mut out,
                format_args!(
                    "(step {implication_id} (cl (not {current}) (not {antecedent}) {consequent}) :rule implies_pos)\n"
                ),
            );
            resolution_premises.push(implication_id);
        }
        let _ = std::fmt::Write::write_fmt(
            &mut out,
            format_args!(
                "(step {id} (cl {}) :rule resolution :premises ({}))",
                printed_clause.join(" "),
                resolution_premises.join(" ")
            ),
        );
        Ok(Some(out))
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

    fn format_anchor(end_step: ProofId, variables: &[(String, Sort)]) -> String {
        let mut result = format!("(anchor :step {end_step}");
        if !variables.is_empty() {
            let vars_str: Vec<String> = variables
                .iter()
                .map(|(name, sort)| format!("({} {sort})", quote_symbol(name)))
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
                self.write_term_into(&mut out, lit);
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
                if let Symbol::Named(n) = sym {
                    if args.len() == 1 {
                        if let Some(ctor) = n.strip_prefix("is-") {
                            return format!(
                                "((_ is {}) {})",
                                quote_symbol(ctor),
                                self.format_term(args[0])
                            );
                        }
                    }
                }
                let name = Self::format_symbol(sym);
                if args.is_empty() {
                    // Alethe's clause constructor is written as `(cl ...)`, including the
                    // empty clause `(cl)`. Printing the 0-arity `cl` application as `cl`
                    // causes Carcara to reject `drup` steps that use `(cl)` terms in `:args`.
                    if matches!(sym, Symbol::Named(s) if s == "cl") {
                        format!("({name})")
                    } else {
                        name
                    }
                } else {
                    let args_str: Vec<String> = args.iter().map(|&a| self.format_term(a)).collect();
                    format!("({} {})", name, args_str.join(" "))
                }
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
            .map(|(name, sort)| format!("({} {})", quote_symbol(name), sort))
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
    ///   - nothing new when the aligned single step is already what the
    ///     default rendering would print (`None`, keeping bytes identical);
    ///   - a single spec-shaped step when only order/variant/position-arg
    ///     differ; or
    ///   - the spec-shaped step + one `not_not` bridge per stripped literal
    ///     (`(cl (not (not (not x))) x)` per the Alethe spec) + a final
    ///     resolution concluding the EXACT traced clause under this step's
    ///     own id, so downstream premise references stay untouched.
    fn format_surface_tautology(
        &self,
        id: ProofId,
        rule: &ay_core::AletheRule,
        clause: &[TermId],
        args: &[TermId],
    ) -> Option<String> {
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
        }
        struct Template {
            rule: &'static str,
            lits: &'static [Lit],
        }
        use Lit::{Operand, Source};

        let source_term = match args {
            [source] => *source,
            // Some tracker-generated and_neg tautologies predate the
            // proof-only source argument. The positive and-term in the clause
            // identifies the source uniquely; strict checking validates the
            // same shape before this printing repair.
            [] if matches!(rule, R::AndNeg) => clause.iter().copied().find(|&term| {
                matches!(
                    self.terms.get(term),
                    TermData::App(Symbol::Named(name), _) if name == "and"
                )
            })?,
            _ => return None,
        };
        let source_str = self.format_term(source_term);

        // Re-deriving from the printed source term re-splits `source_str`
        // per template and clones its operand vector per position; on huge
        // printed terms (QF_ALIA pp-family) this is the emission hotspot.
        // Charge the split cost and fall back to the generic rendering once
        // the synthesized-default work budget is exhausted (#A2b) — the
        // caller's per-step check then degrades to the honest
        // "no certificate emitted" warning.
        self.charge(source_str.len() as u64);
        if self.work_budget_exhausted() {
            return None;
        }

        // Spec templates per rule family (Alethe spec, "Tautologous rules"),
        // keyed by the printed operator. `or`-family rules also try `=>`:
        // elaboration desugars implications to or-terms, and the printed
        // surface form is the implication.
        let n_ary_positions = |n: usize| 0..n;
        let mut candidates: Vec<(Vec<String>, Template)> = Vec::new();
        let mut push_for_op = |op: &str, templates: Vec<Template>| {
            if let Some(ops) = split_application(&source_str, op) {
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
        const EQUIV_NEG1: &[Lit] = &[Source(false), Operand(0, false), Operand(1, false)];
        const EQUIV_NEG2: &[Lit] = &[Source(false), Operand(0, true), Operand(1, true)];
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
                    return Some(text);
                }
            }
            R::OrNeg => {
                if let Some(ops) = split_application(&source_str, "or") {
                    // One cloned operand vector per position: quadratic in
                    // the printed operand bytes. Charge upfront (#A2b).
                    let ops_bytes: u64 = ops.iter().map(|o| o.len() as u64).sum();
                    self.charge(ops_bytes.saturating_mul(ops.len() as u64));
                    if self.work_budget_exhausted() {
                        return None;
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
                        return None;
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
            R::ImpliesPos => push_for_op("=>", vec![template("implies_pos", IMPLIES_POS)]),
            R::ImpliesNeg1 => push_for_op("=>", vec![template("implies_neg1", IMPLIES_NEG1)]),
            R::ImpliesNeg2 => push_for_op("=>", vec![template("implies_neg2", IMPLIES_NEG2)]),
            _ => return None,
        }
        for (ops, t) in candidates {
            positional.push((ops, t.rule, t.lits.to_vec(), usize::MAX));
        }

        // The printed traced clause, as literal strings.
        let printed: Vec<String> = clause.iter().map(|&l| self.format_term(l)).collect();
        let mut printed_sorted = printed.clone();
        printed_sorted.sort_unstable();

        for (ops, rule_name, lits, position) in positional {
            // Instantiating a template copies roughly the operand bytes;
            // stop matching once the emission budget is gone (#A2b).
            self.charge(ops.iter().map(|o| o.len() as u64).sum());
            if self.work_budget_exhausted() {
                return None;
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
                        Some(op) => (op.clone(), op.clone()),
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
                                    if printed.iter().any(|lit| lit == &s) {
                                        (s.clone(), s)
                                    } else if let Some(dual) = surface_order_negation(op) {
                                        if !printed.iter().any(|lit| lit == &dual) {
                                            (s.clone(), s)
                                        } else {
                                            bridges.push(Bridge::LinearOrder {
                                                operand: op.clone(),
                                                dual: dual.clone(),
                                            });
                                            (s, dual)
                                        }
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
                    return None;
                }
                return Some(format!(
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
            return Some(out);
        }
        None
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
    /// Taken only when the printed traced clause is exactly that multiset;
    /// `None` keeps the default rendering.
    fn format_not_and_or_pos(
        &self,
        id: ProofId,
        clause: &[TermId],
        source_str: &str,
    ) -> Option<String> {
        let (and_str, conjuncts) = split_not_and_full(source_str)?;
        let not_source = format!("(not {source_str})");
        let neg_conjuncts: Vec<String> = conjuncts.iter().map(|a| format!("(not {a})")).collect();
        let mut expected: Vec<String> = std::iter::once(not_source.clone())
            .chain(neg_conjuncts.iter().cloned())
            .collect();
        let printed: Vec<String> = clause.iter().map(|&l| self.format_term(l)).collect();
        let mut printed_sorted = printed.clone();
        printed_sorted.sort_unstable();
        expected.sort_unstable();
        if printed_sorted != expected {
            return None;
        }
        let eq = format!("(= {not_source} {and_str})");
        Some(format!(
            "(step {id}a (cl {eq}) :rule not_simplify)\n\
             (step {id}b (cl (not {eq}) {not_source} (not {and_str})) :rule equiv_pos1)\n\
             (step {id}c (cl {and_str} {}) :rule and_neg)\n\
             (step {id} (cl {}) :rule resolution :premises ({id}a {id}b {id}c))",
            neg_conjuncts.join(" "),
            printed.join(" ")
        ))
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

/// Split a rendered application string `(op A1 ... An)` into its top-level
/// argument strings by balanced-token scanning. Returns `None` when `s` is
/// not an application of `op`.
fn split_application(s: &str, op: &str) -> Option<Vec<String>> {
    split_alethe_application_bounded(s, op, usize::MAX, usize::MAX)
        .ok()
        .map(|arguments| arguments.into_iter().map(str::to_string).collect())
}

/// Split the *body* of an s-expression into its top-level tokens by balanced
/// scanning. `inner` is everything between the outermost parentheses; unlike
/// [`split_application`] no leading operator is stripped, so this also serves
/// binding lists (`(?v_0 e0) (?v_1 e1)`). Returns `None` on unbalanced input.
fn split_sexpr_tokens(inner: &str) -> Option<Vec<String>> {
    split_smt_terms(inner)
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
    if !inner.starts_with(|c: char| c.is_whitespace()) {
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

/// Textually replace whole-token occurrences of each bound name by its value.
///
/// Token boundaries are the s-expression delimiters (parens / whitespace) with
/// `|quoted symbols|` treated as atomic, so a binding named `?v_1` never
/// rewrites the inside of `?v_12` or of a quoted symbol.
fn substitute_printed_tokens(text: &str, bindings: &[(String, String)]) -> String {
    let mut out = String::with_capacity(text.len());
    let mut token = String::new();
    let mut in_quote = false;
    let flush = |token: &mut String, out: &mut String| {
        if token.is_empty() {
            return;
        }
        match bindings.iter().find(|(name, _)| name == token) {
            Some((_, value)) => out.push_str(value),
            None => out.push_str(token),
        }
        token.clear();
    };
    for c in text.chars() {
        match c {
            '|' => {
                in_quote = !in_quote;
                token.push(c);
            }
            _ if in_quote => token.push(c),
            '(' | ')' => {
                flush(&mut token, &mut out);
                out.push(c);
            }
            c if c.is_whitespace() => {
                flush(&mut token, &mut out);
                out.push(c);
            }
            _ => token.push(c),
        }
    }
    flush(&mut token, &mut out);
    out
}

/// `true` when a peeled `let` chain can be expanded by plain token
/// substitution: no name is bound at two levels (shadowing), and no level's
/// binding VALUES mention a name that same level binds (SMT-LIB `let` binds in
/// PARALLEL, so such an occurrence refers to an outer symbol, not the binding).
fn printed_let_bindings_are_simple(levels: &[PrintedLetLevel]) -> bool {
    let mut seen: Vec<&str> = Vec::new();
    for (bindings, _) in levels {
        for (name, _) in bindings {
            if seen.contains(&name.as_str()) {
                return false;
            }
            seen.push(name.as_str());
        }
        for (_, value) in bindings {
            let rewritten = substitute_printed_tokens(value, bindings);
            if rewritten != *value {
                return false;
            }
        }
    }
    true
}

/// Fully expand a peeled `let` chain: substitute innermost bindings first so
/// that an inner binding value mentioning an outer variable is itself expanded
/// by the outer pass.
fn expand_printed_lets(levels: &[PrintedLetLevel], innermost_body: &str) -> String {
    let mut expanded = innermost_body.to_string();
    for (bindings, _) in levels.iter().rev() {
        expanded = substitute_printed_tokens(&expanded, bindings);
    }
    expanded
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
