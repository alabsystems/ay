// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Alethe proof format printer.
//!
//! Formats proof steps, clauses, terms, and constants as SMT-LIB/Alethe text.

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
    /// Internal clauses by proof id, populated eagerly so a resolution step
    /// can repair surface-order complements in its already-printed premises.
    proof_clauses: std::cell::RefCell<HashMap<ProofId, Vec<TermId>>>,
    /// Accumulated rendering work (abstract units, roughly bytes touched by
    /// term formatting and surface-tautology re-derivation). See
    /// [`AlethePrintError::EmissionBudgetExhausted`].
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
            let choice = format!(
                "(choice (({} {})) (not {}))",
                binder_token, binder_sort, body_surface
            );
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
        // Preparation may have formatted source terms before their substituted
        // overrides were installed. Never retain a stale rendering.
        self.format_cache.borrow_mut().clear();
        Ok(())
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
        // The internal conjunct index `i` must be valid against the PRINTED
        // and-term. A surface override can re-spell `source` (e.g. re-nest a
        // flattened conjunction, or reorder commutative args), so the printed
        // arity / operand-`i` may diverge from the internal conjunct vector —
        // emitting `:args (i)` against a divergent printed shape yields a
        // wrong-index step. Require the printed `and` to split into exactly the
        // internal conjunct count with operand `i` equal to `Ak`.
        let printed_ops = split_application(&source_str, "and")?;
        if printed_ops.len() != conjuncts.len() || printed_ops.get(i) != Some(&ak_str) {
            return None;
        }
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
        Some(format!(
            "(step {id} (cl (not {source_str}) {ak_str}) :rule and_pos :args ({i}))"
        ))
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

    /// Record `amount` units of rendering work (saturating).
    fn charge(&self, amount: u64) {
        self.work.set(self.work.get().saturating_add(amount));
    }

    /// `true` once accumulated work exceeds the configured budget (never
    /// `true` when unbudgeted).
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
    /// verifiable rule — currently this only fires for `LraFarkas` / `LiaGeneric`
    /// theory lemmas that are missing their `FarkasAnnotation` (#8821). The
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
                let term_str = self.format_term(*term_id);
                Ok(format!("(assume {id} {term_str})"))
            }
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => Ok(self.format_resolution_step(id, clause, *pivot, *clause1, *clause2)),
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                kind,
                ..
            } => self.format_theory_lemma(id, theory, clause, farkas.as_ref(), kind),
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } if matches!(rule, ay_core::AletheRule::Skolem) => {
                self.format_certified_skolem_step(id, clause, premises, args)
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => Ok(self.format_generic_step(id, rule, clause, premises, args)),
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
    ) -> String {
        // A binary `(distinct a b)` literal is AY's internal spelling of
        // `(not (= a b))`, but Carcara's resolution treats it as an opaque
        // atom, so a resolution that cancels `(distinct a b)` against an
        // equality `(= a b)` / `(= b a)` reports "pivot was not eliminated".
        // Bridge it honestly with `distinct_elim` (+ `symm` for the swapped
        // argument order) before falling through to the generic rendering.
        if let Some(text) = self.distinct_eq_resolution_bridge(id, clause, clause1, clause2) {
            return text;
        }
        if let Some((left, right)) =
            self.surface_order_resolution_pair(clause, pivot, clause1, clause2)
        {
            return format!(
                "(step {id}.ord (cl (not {left}) (not {right})) :rule la_generic :args (1 1))\n\
                 (step {id} {} :rule resolution :premises ({clause1} {id}.ord {clause2}))",
                self.format_clause(clause)
            );
        }

        // Omit :args — Carcara infers an ordinary syntactic pivot from the
        // premises.
        format!(
            "(step {id} {} :rule resolution :premises ({clause1} {clause2}))",
            self.format_clause(clause)
        )
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
                    .filter_map(|(i, &l)| (i != didx).then(|| self.format_term(l)))
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

    fn format_theory_lemma(
        &self,
        id: ProofId,
        theory: &str,
        clause: &[TermId],
        farkas: Option<&ay_core::FarkasAnnotation>,
        kind: &ay_core::TheoryLemmaKind,
    ) -> Result<String, AlethePrintError> {
        let clause_str = self.format_clause(clause);
        if let Some(farkas) = farkas {
            let rule = kind.alethe_rule();
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

        // An `eq_transitive` clause whose negated-equality hypotheses print
        // in AY's `(distinct a b)` surface spelling (or which degenerates to
        // the two-literal symmetry tautology) is not spec-valid Alethe:
        // Carcara requires every hypothesis to be a literal `(not (= t u))`
        // and requires at least two of them. Rebuild it from the canonical
        // `(not (= …))` forms plus reflexive padding, then bridge each
        // hypothesis back to its printed `(distinct …)` spelling with
        // `distinct_elim`/`equiv2` so the step's final clause is byte-identical
        // and every downstream premise reference is unaffected. Emission-only.
        if kind.alethe_rule() == "eq_transitive" {
            if let Some(text) = self.resugar_eq_transitive(id, clause) {
                return Ok(text);
            }
        }

        // Non-arithmetic kinds fall through to their own rule name. Any
        // theory lemma whose rule is the literal `"trust"` (i.e.,
        // TheoryLemmaKind::Generic) is emitted faithfully so the #8759
        // detector sees the trust step via `kind.is_trust()`.
        Ok(format!(
            "(step {id} {clause_str} :rule {})",
            kind.alethe_rule()
        ))
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
                && !(info.canonical.starts_with("(not (= ") || info.distinct.is_some())
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
    ) -> String {
        // A `th_resolution`/`resolution` step that cancels a printed
        // `(distinct a b)` literal against an equality unit clause is not
        // spec-valid Alethe over the printed premise (Carcara sees the
        // `distinct` atom as opaque and reports "pivot was not eliminated").
        // `ProofStep::Resolution` already routes through the same bridge in
        // `format_resolution_step`; the n-ary `th_resolution` generic step
        // needs it too. The bridge returns `None` (falling through to the
        // ordinary rendering) unless it detects a `distinct`↔`(= …)`
        // cancellation, so ordinary resolutions are byte-unchanged.
        if premises.len() == 2
            && matches!(
                rule,
                ay_core::AletheRule::ThResolution | ay_core::AletheRule::Resolution
            )
        {
            if let Some(text) =
                self.distinct_eq_resolution_bridge(id, clause, premises[0], premises[1])
            {
                return text;
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
                return text;
            }
            // Equality-split extraction: elaboration lowers an arithmetic
            // equality `(= L R)` to the conjunction `(and (<= ..) (<= ..))`
            // (printed back as `(= L R)` via its surface override) and
            // Tseitin annotates the one-sided extraction as `and_pos` — but
            // `and_pos` over a printed equality is not spec-valid Alethe.
            // The spec-correct rule for the printed shape is a certified
            // `la_generic` orientation lemma (#relu-trust-glue).
            if let Some(text) = self.resugar_equality_split_and_pos(id, rule, clause) {
                return text;
            }
            // `and_pos` whose `(not (and ...))` gate literal was traced as its
            // De Morgan surface `(or (not A1) .. (not An))`: re-slot to the
            // spec-shaped `(cl (not (and ...)) Ak)` Carcara requires.
            if let Some(text) = self.resugar_and_pos_not_and(id, rule, clause, args) {
                return text;
            }
            // Clausification tautologies over a source term whose PRINTED
            // form diverges from the internal canonical form (surface-syntax
            // overrides reordering commutative arguments, `=>` desugared to
            // an or-term) — or whose traced literals were double-negation
            // stripped (`a` where strict Alethe wants `(not (not a))`) —
            // are re-derived from the printed operands: the spec-shaped
            // tautology, `not_not` bridge steps for each stripped literal,
            // and a final resolution restoring the exact traced clause.
            if let Some(text) = self.format_surface_tautology(id, rule, clause, args) {
                return text;
            }
        }
        // An `or` decomposition step whose premise assume PRINTS as a De
        // Morgan surface form `(not (and A1 .. An))` (elaboration
        // canonicalizes that input to the or-term `(or (not A1) .. (not An))`)
        // is not spec-valid Alethe over the printed premise; the spec-correct
        // rule for the printed shape is `not_and`.
        if matches!(rule, ay_core::AletheRule::Or) && premises.len() == 1 {
            if let Some(text) = self.resugar_not_and_decomposition(id, clause, premises[0]) {
                return text;
            }
        }
        let clause_str = self.format_clause(clause);
        let mut result = format!("(step {id} {clause_str} :rule {rule}");
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
        result
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

    /// Format a term as an SMT-LIB expression
    pub(crate) fn format_term(&self, term_id: TermId) -> String {
        let mut out = String::new();
        self.write_term_into(&mut out, term_id);
        out
    }

    /// Append the rendering of `term_id` to `out`.
    ///
    /// Same semantics (including #A2b work-budget charging) as
    /// [`Self::format_term`], but a cache hit copies the cached bytes
    /// straight into the caller's buffer instead of allocating an owned
    /// clone first (#proof-tax).
    fn write_term_into(&self, out: &mut String, term_id: TermId) {
        // #A2b: once the emission work budget is exhausted the whole
        // document is guaranteed to be DISCARDED (the export loop returns
        // `EmissionBudgetExhausted` at the next step boundary — `work` never
        // decreases), so cut the recursion short instead of grinding through
        // gigabytes of string building for output nobody will see. The
        // placeholder never reaches disk.
        if self.work_budget_exhausted() {
            out.push_str("@a2b_emission_budget_exhausted");
            return;
        }
        if let Some(term_str) = self.skolem_overrides.borrow().get(&term_id).cloned() {
            self.charge(term_str.len() as u64);
            out.push_str(&term_str);
            return;
        }
        if let Some(term_str) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&term_id))
        {
            self.charge(term_str.len() as u64);
            out.push_str(term_str);
            return;
        }
        if let Some(cached) = self.format_cache.borrow().get(&term_id) {
            // A cache hit still copies the rendered bytes; on proofs whose
            // steps repeat megabyte literals that copy IS the dominant cost,
            // so it is charged against the emission work budget (#A2b).
            self.charge(cached.len() as u64);
            out.push_str(cached);
            return;
        }
        let term = self.terms.get(term_id);
        let formatted = self.format_term_data(term);
        self.charge(formatted.len() as u64);
        out.push_str(&formatted);
        self.format_cache.borrow_mut().insert(term_id, formatted);
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
            R::AndPos(_) => {
                if let Some(ops) = split_application(&source_str, "and") {
                    let ops_bytes: u64 = ops.iter().map(|o| o.len() as u64).sum();
                    self.charge(ops_bytes.saturating_mul(ops.len() as u64));
                    if self.work_budget_exhausted() {
                        return None;
                    }
                    for k in n_ary_positions(ops.len()) {
                        positional.push((
                            ops.clone(),
                            "and_pos",
                            vec![Source(true), Operand(k, false)],
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

/// Split an SMT-LIB fragment into balanced top-level terms.
fn split_smt_terms(s: &str) -> Option<Vec<String>> {
    let chars: Vec<char> = s.chars().collect();
    let mut terms = Vec::new();
    let mut start = None;
    let mut depth = 0usize;
    let mut index = 0usize;
    let mut in_quoted_symbol = false;
    let mut in_string = false;
    while index < chars.len() {
        let c = chars[index];
        if in_string {
            if c == '"' {
                if index + 1 < chars.len() && chars[index + 1] == '"' {
                    index += 2;
                    continue;
                }
                in_string = false;
            }
            index += 1;
            continue;
        }
        if in_quoted_symbol {
            if c == '|' {
                in_quoted_symbol = false;
            }
            index += 1;
            continue;
        }
        match c {
            '"' => {
                start.get_or_insert(index);
                in_string = true;
            }
            '|' => {
                start.get_or_insert(index);
                in_quoted_symbol = true;
            }
            '(' => {
                start.get_or_insert(index);
                depth += 1;
            }
            ')' => {
                depth = depth.checked_sub(1)?;
            }
            c if c.is_whitespace() && depth == 0 => {
                if let Some(term_start) = start.take() {
                    terms.push(chars[term_start..index].iter().collect());
                }
            }
            _ => {
                start.get_or_insert(index);
            }
        }
        index += 1;
    }
    if depth != 0 || in_quoted_symbol || in_string {
        return None;
    }
    if let Some(term_start) = start {
        terms.push(chars[term_start..].iter().collect());
    }
    Some(terms)
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

/// Split a rendered application string `(op A1 ... An)` into its top-level
/// argument strings by balanced-token scanning. Returns `None` when `s` is
/// not an application of `op`.
fn split_application(s: &str, op: &str) -> Option<Vec<String>> {
    let inner = s.strip_prefix('(')?.strip_prefix(op)?.strip_suffix(')')?;
    // Require a token boundary after the operator (rejects e.g. `(orx ...)`
    // when splitting on "or").
    if !inner.starts_with(|c: char| c.is_whitespace()) {
        return None;
    }
    let mut tokens: Vec<String> = Vec::new();
    let mut depth = 0usize;
    let mut current = String::new();
    let mut in_quote = false;
    for c in inner.chars() {
        match c {
            '|' => {
                in_quote = !in_quote;
                current.push(c);
            }
            _ if in_quote => current.push(c),
            '(' => {
                depth += 1;
                current.push(c);
            }
            ')' => {
                depth = depth.checked_sub(1)?;
                current.push(c);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            }
            _ => current.push(c),
        }
    }
    if depth != 0 || in_quote {
        return None;
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    Some(tokens)
}

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
