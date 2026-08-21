// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{
    AletheRule, Proof, ProofId, ProofStep, TermData, TermId, TermStore, TheoryLemmaKind,
};
use ay_sat::ResolutionValidationError;

use super::types::OrFoldUnitPlan;
use crate::sat_proof_manager::{
    ExactOriginalProofError, FragmentInstanceDerivation, SatProofManager,
};

/// Premise-chaining recursion bound for #dt-context-derivation: a stripped
/// level-0 premise may itself be a sealed context-derived unit (an injected
/// extra), whose own premises may chain once more. Depth exhaustion declines
/// fail-closed.
const CONTEXT_DERIVATION_MAX_DEPTH: usize = 8;

impl SatProofManager<'_> {
    pub(in crate::sat_proof_manager) fn emit_indexed_original_step(
        &mut self,
        proof: &mut Proof,
        clause_id: u64,
        clause: &[TermId],
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let clausification = Self::original_annotation_by_id(self.clausification_proofs, clause_id);
        let theory = Self::original_annotation_by_id(self.original_clause_theory_proofs, clause_id);
        match (clausification, theory) {
            (Some(_), Some(_)) => {
                Err(ExactOriginalProofError::AmbiguousIndexedAnnotations { clause_id })
            }
            (Some(annotation), None) => {
                if annotation.source_term.index() >= self.terms.len() {
                    return Err(ExactOriginalProofError::InvalidClausificationAnnotation {
                        clause_id,
                        clause: Self::normalize_clause(clause),
                    });
                }
                let (work, bytes) =
                    self.clausification_preflight(annotation.source_term, clause.len())?;
                progress(work, bytes)?;
                let Some(step_clause) = Self::canonicalize_tautology_clause(
                    self.terms,
                    &annotation.rule,
                    annotation.source_term,
                    clause,
                ) else {
                    return Err(ExactOriginalProofError::InvalidClausificationAnnotation {
                        clause_id,
                        clause: Self::normalize_clause(clause),
                    });
                };
                self.reconcile_term_store_growth(
                    term_store_baseline,
                    charged_term_store_growth,
                    progress,
                )?;
                Ok(Some(proof.add_rule_step(
                    annotation.rule.clone(),
                    step_clause,
                    Vec::new(),
                    vec![annotation.source_term],
                )))
            }
            (None, Some(annotation)) => {
                let (work, bytes) = Self::theory_annotation_preflight(annotation, clause.len())?;
                progress(work, bytes)?;
                if !Self::clauses_equivalent(&annotation.clause, clause) {
                    return Err(ExactOriginalProofError::InvalidTheoryAnnotation {
                        clause_id,
                        clause: Self::normalize_clause(clause),
                    });
                }
                let Some(annotation) = Self::rebind_theory_annotation(annotation, clause) else {
                    return Err(ExactOriginalProofError::InvalidTheoryAnnotation {
                        clause_id,
                        clause: Self::normalize_clause(clause),
                    });
                };
                Ok(Some(proof.add_step(ProofStep::TheoryLemma {
                    theory: "theory".to_owned(),
                    clause: annotation.clause,
                    farkas: annotation.farkas,
                    kind: annotation.kind,
                    lia: annotation.lia,
                })))
            }
            (None, None) => Ok(None),
        }
    }

    fn emit_basic_original_unit(
        &mut self,
        proof: &mut Proof,
        unit: TermId,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_bool_ites: &[(TermId, TermId, TermId)],
        unit_authority: bool,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if authored_terms.contains(&unit) || (unit_authority && authored_conjuncts.contains(&unit))
        {
            return Ok(Some(proof.add_assume(unit, None)));
        }
        // #ite-expansion-authority: `rewrite_assertion_bool_ites` products are
        // ENTAILED branch implications of an authored Bool ITE. Recognition is
        // the strict checker's own shared matcher, so the checker's premise
        // validator independently re-accepts exactly what is assumed here.
        if unit_authority
            && ay_proof::assumed_is_authored_bool_ite_consequence(
                self.terms,
                unit,
                authored_bool_ites,
            )
        {
            let (work, bytes) = Self::unit_chain_charge(1, 1)?;
            progress(work, bytes)?;
            return Ok(Some(proof.add_assume(unit, None)));
        }
        if unit_authority && Self::is_closed_bool_tautology_unit(self.terms, unit) {
            let (work, bytes) = Self::unit_chain_charge(1, 1)?;
            progress(work, bytes)?;
            return Ok(Some(proof.add_rule_step(
                AletheRule::True,
                vec![unit],
                Vec::new(),
                Vec::new(),
            )));
        }
        if unit_authority && Self::is_closed_ground_comparison_unit(self.terms, unit) {
            let (work, bytes) = Self::unit_chain_charge(5, 8)?;
            progress(work, bytes)?;
            let step = Self::emit_closed_eval_unit_chain(self.terms, proof, unit);
            self.reconcile_term_store_growth(
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )?;
            return Ok(Some(step));
        }
        Ok(None)
    }

    fn emit_sealed_original_unit(
        &mut self,
        proof: &mut Proof,
        unit: TermId,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        unit_chain_memo: &mut HashMap<TermId, ProofId>,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if let Some(&memoized) = unit_chain_memo.get(&unit) {
            return Ok(Some(memoized));
        }
        if let Some(derivation) = self.instance_derivations.and_then(|map| map.get(&unit)) {
            let derivation = derivation.clone();
            if (authored_terms.contains(&derivation.quantifier)
                || authored_conjuncts.contains(&derivation.quantifier))
                && (derivation.instance == unit || unit == self.terms.false_term())
            {
                let step = Self::emit_forall_inst_unit_chain(
                    self.terms,
                    proof,
                    &derivation,
                    unit,
                    progress,
                )?;
                self.reconcile_term_store_growth(
                    term_store_baseline,
                    charged_term_store_growth,
                    progress,
                )?;
                unit_chain_memo.insert(unit, step);
                return Ok(Some(step));
            }
        }
        if let Some(derivation) = self.skolem_derivations.and_then(|map| map.get(&unit)) {
            let derivation = derivation.clone();
            if authored_terms.contains(&derivation.source)
                || authored_conjuncts.contains(&derivation.source)
            {
                let step =
                    Self::emit_skolem_unit_chain(self.terms, proof, &derivation, unit, progress)?;
                self.reconcile_term_store_growth(
                    term_store_baseline,
                    charged_term_store_growth,
                    progress,
                )?;
                return Ok(Some(step));
            }
        }
        Ok(None)
    }

    pub(in crate::sat_proof_manager) fn emit_unannotated_original_step(
        &mut self,
        proof: &mut Proof,
        clause_id: u64,
        clause: &[TermId],
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_bool_ites: &[(TermId, TermId, TermId)],
        authored_problem_terms: &[TermId],
        or_fold_unit_plans: &HashMap<TermId, OrFoldUnitPlan>,
        unit_chain_memo: &mut HashMap<TermId, ProofId>,
        unit_authority: bool,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ProofId, ExactOriginalProofError> {
        if let [unit] = clause {
            if let Some(step) = self.emit_basic_original_unit(
                proof,
                *unit,
                authored_terms,
                authored_conjuncts,
                authored_bool_ites,
                unit_authority,
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )? {
                return Ok(step);
            }
            if unit_authority {
                if let Some(step) = self.emit_sealed_original_unit(
                    proof,
                    *unit,
                    authored_terms,
                    authored_conjuncts,
                    unit_chain_memo,
                    term_store_baseline,
                    charged_term_store_growth,
                    progress,
                )? {
                    return Ok(step);
                }
                if let Some(plan) = or_fold_unit_plans.get(unit) {
                    let plan = plan.clone();
                    let step =
                        Self::emit_or_fold_unit_chain(self.terms, proof, &plan, *unit, progress)?;
                    self.reconcile_term_store_growth(
                        term_store_baseline,
                        charged_term_store_growth,
                        progress,
                    )?;
                    return Ok(step);
                }
                // Replay a sealed PropagateValues unit when available (#ppp-c7).
                if let Some(step) = self.emit_propagated_unit_chain(
                    proof,
                    *unit,
                    authored_terms,
                    authored_problem_terms,
                    unit_chain_memo,
                    term_store_baseline,
                    charged_term_store_growth,
                    progress,
                )? {
                    return Ok(step);
                }
                if let Some(step) = self.emit_intrinsic_original_unit(proof, *unit, progress)? {
                    return Ok(step);
                }
            }
        }
        if let Some(step) = self.emit_intrinsic_original_clause(proof, clause, progress)? {
            return Ok(step);
        }
        // #dt-context-derivation: sealed premise-carrying authentication for
        // clauses entailed only UNDER the problem's other constraints (the
        // lazy-DT lane's variable-indirection selector/tester units and the
        // extension's mid-solve propagation clauses). The sealed record only
        // NAMES the premises; validity of the widened clause is re-derived
        // here by the bounded ground refuter and every premise is discharged
        // as an authored assumption, so nothing producer-side is trusted.
        if let Some(step) = self.emit_context_derivation_chain(
            proof,
            clause,
            authored_terms,
            authored_conjuncts,
            unit_authority,
            unit_chain_memo,
            CONTEXT_DERIVATION_MAX_DEPTH,
            term_store_baseline,
            charged_term_store_growth,
            progress,
        )? {
            return Ok(step);
        }
        // GROUND-ENCODING SUBSTITUTION BRIDGE (#letleak wall 3): an or-packed
        // unit that is a sealed quantifier instance with authored ground
        // equalities substituted through it — re-derived as
        // assume(equalities) + forall_inst replay + the strict
        // `GroundEqualitySubstitution` lemma (parallel-walk validated).
        if let [unit] = clause {
            if let Some(step) = self.emit_ground_substituted_instance_unit(
                proof,
                *unit,
                authored_terms,
                authored_conjuncts,
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )? {
                return Ok(step);
            }
        }
        // The SHAPE of the clause no authority lane could authenticate is the
        // one fact a certification-decline triage needs, and the typed error
        // names only ids. Same rationale as the `GENERIC lemma declined`
        // disclosure in `ay-proof`'s checker: without the rendered literals a
        // triage cannot tell a missing authority LANE (the clause is a
        // preprocessing product with a derivable pedigree) from a producer
        // defect. Gated on the typed `--probe-cert-reject` carrier.
        if ay_core::misc_cli_flags().probe_cert_reject {
            for &lit in clause {
                ay_core::safe_eprintln!(
                    "--probe-cert-reject: unauthenticated original clause {clause_id} literal: {}",
                    ay_proof::render_term_canonical(self.terms, lit)
                );
            }
            let n = self.instance_derivations.map_or(0, HashMap::len);
            let env_records = self
                .propagation_environment
                .map_or(0, |env| env.record_by_after.len());
            let env_entries = self
                .propagation_environment
                .map_or(0, |env| env.entry_by_expr.len());
            ay_core::safe_eprintln!(
                "--probe-cert-reject: instance_derivations available: {n} propagation_env: records_by_after={env_records} entries_by_expr={env_entries}"
            );
            if let Some(map) = self.instance_derivations {
                for (key, derivation) in map.iter().take(8) {
                    ay_core::safe_eprintln!(
                        "--probe-cert-reject: recorded instance key={} quantifier={} instance={}",
                        ay_proof::render_term_canonical(self.terms, *key),
                        ay_proof::render_term_canonical(self.terms, derivation.quantifier),
                        ay_proof::render_term_canonical(self.terms, derivation.instance),
                    );
                }
            }
        }
        Err(ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id,
            clause: Self::normalize_clause(clause),
        })
    }

    /// #dt-context-derivation: authenticate one original clause through a
    /// sealed premise-carrying derivation.
    ///
    /// Emitted sequence, all independently re-validated by the strict
    /// checker: one `TheoryLemma` with kind `DatatypeGroundConflict` whose
    /// clause is the WIDENED form `clause ∨ ¬P_1 ∨ .. ∨ ¬P_k` (the ground
    /// refuter must refute its negation — i.e. the premises entail the
    /// clause within ground DT/EUF reasoning), one `Assume` per premise
    /// (authored assertions or, campaign-gated, authored `and`-conjuncts —
    /// exactly the metered strict validator's closure), and `k` binary
    /// resolutions recovering the traced clause literal-for-literal.
    ///
    /// Fail-closed: no sealed record for the normalized clause, no datatype
    /// registries, an unauthored premise, a premise/literal parity collision
    /// (which would make the retain-based resolvent over-remove), or a
    /// refuter decline all return `None` and the caller falls through to the
    /// typed error.
    #[allow(clippy::too_many_arguments)]
    fn emit_context_derivation_chain(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        unit_authority: bool,
        unit_chain_memo: &mut HashMap<TermId, ProofId>,
        depth: usize,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        use ay_core::TermData;
        let Some(derivations) = self.context_derivations else {
            return Ok(None);
        };
        let Some(registry) = self.dt_registry_data else {
            return Ok(None);
        };
        let key = Self::normalize_clause(clause);
        let Some(derivation) = derivations.get(&key) else {
            if std::env::var("AY_DT_DEBUG").is_ok() {
                eprintln!(
                    "c context-lane-debug decline=no-record lits={}",
                    clause.len()
                );
            }
            return Ok(None);
        };
        let premises = derivation.premises.clone();
        if premises.is_empty() {
            return Ok(None);
        }
        // Discharge every premise FIRST (steps must be strictly prior to the
        // resolutions consuming them). A premise is discharged as an Assume
        // (authored / campaign-gated conjunct closure), a standalone typed
        // unit lemma, or — bounded by `depth` — a chained context derivation
        // of its own (the stripped level-0 facts are often themselves
        // solver-injected units with sealed records). Any failure declines
        // the whole lane fail-closed.
        let mut premise_steps: Vec<ProofId> = Vec::with_capacity(premises.len());
        for &premise in &premises {
            let Some(step) = self.emit_context_premise_step(
                proof,
                premise,
                authored_terms,
                authored_conjuncts,
                unit_authority,
                unit_chain_memo,
                depth,
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )?
            else {
                if std::env::var("AY_DT_DEBUG").is_ok() {
                    eprintln!(
                        "c context-lane-debug decline=premise lits={} depth={depth}",
                        clause.len()
                    );
                }
                return Ok(None);
            };
            premise_steps.push(step);
        }
        // Widen with the parity negation of every premise. A negation that
        // already occurs among the trace literals (or repeats) would make
        // the resolution retain step remove a literal the conclusion needs.
        let clause_literals: ay_core::kani_compat::DetHashSet<TermId> =
            clause.iter().copied().collect();
        let mut widened = clause.to_vec();
        let mut negated: Vec<TermId> = Vec::with_capacity(premises.len());
        for &premise in &premises {
            let negation = match self.terms.get(premise) {
                TermData::Not(inner) => *inner,
                _ => self.terms.mk_not(premise),
            };
            if clause_literals.contains(&negation) || negated.contains(&negation) {
                return Ok(None);
            }
            negated.push(negation);
            widened.push(negation);
        }
        self.reconcile_term_store_growth(term_store_baseline, charged_term_store_growth, progress)?;
        // Recognition IS the strict validator: acceptance here is re-decided
        // identically when the checker re-validates the emitted lemma.
        let view = crate::theory_inference::DatatypeRegistries::from_data(registry);
        if !ay_proof::recognize_datatype_ground_conflict(
            self.terms,
            &widened,
            view.datatypes,
            view.ctor_selectors,
        ) {
            if std::env::var("AY_DT_DEBUG").is_ok() {
                eprintln!(
                    "c context-lane-debug decline=refuter lits={} premises={}",
                    clause.len(),
                    premises.len()
                );
            }
            return Ok(None);
        }
        let (work, bytes) =
            Self::unit_chain_charge(1 + 2 * premises.len(), widened.len() + premises.len())?;
        progress(work, bytes)?;
        let mut previous = proof.add_step(ProofStep::TheoryLemma {
            theory: "dt".to_owned(),
            clause: widened.clone(),
            farkas: None,
            kind: TheoryLemmaKind::DatatypeGroundConflict,
            lia: None,
        });
        let mut remaining = widened;
        for ((&premise, &negation), &premise_step) in
            premises.iter().zip(&negated).zip(&premise_steps)
        {
            remaining.retain(|&literal| literal != negation);
            let pivot = match self.terms.get(premise) {
                TermData::Not(inner) => *inner,
                _ => premise,
            };
            previous = proof.add_resolution(remaining.clone(), pivot, previous, premise_step);
        }
        Ok(Some(previous))
    }

    /// Discharge one #dt-context-derivation premise as a step concluding
    /// `(cl premise)`. Memoized per premise term (shared across the many
    /// conflict chains that repeat the same level-0 facts).
    #[allow(clippy::too_many_arguments)]
    fn emit_context_premise_step(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        unit_authority: bool,
        unit_chain_memo: &mut HashMap<TermId, ProofId>,
        depth: usize,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if let Some(&step) = unit_chain_memo.get(&premise) {
            return Ok(Some(step));
        }
        // Authored assumption closure — exactly what the metered strict
        // validator accepts for Assume steps.
        if authored_terms.contains(&premise)
            || (unit_authority && authored_conjuncts.contains(&premise))
        {
            let (work, bytes) = Self::unit_chain_charge(1, 1)?;
            progress(work, bytes)?;
            let step = proof.add_assume(premise, None);
            unit_chain_memo.insert(premise, step);
            return Ok(Some(step));
        }
        if depth == 0 {
            return Ok(None);
        }
        // Standalone typed unit tautology against the registries.
        if let Some(registry) = self.dt_registry_data {
            let view = crate::theory_inference::DatatypeRegistries::from_data(registry);
            if let Some(kind) =
                crate::theory_inference::infer_dt_lemma_kind(self.terms, &[premise], &view)
            {
                let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                progress(work, bytes)?;
                let step = proof.add_step(ProofStep::TheoryLemma {
                    theory: "dt".to_owned(),
                    clause: vec![premise],
                    farkas: None,
                    kind,
                    lia: None,
                });
                unit_chain_memo.insert(premise, step);
                return Ok(Some(step));
            }
        }
        // Chained context derivation of the premise's own unit clause.
        let step = self.emit_context_derivation_chain(
            proof,
            &[premise],
            authored_terms,
            authored_conjuncts,
            unit_authority,
            unit_chain_memo,
            depth - 1,
            term_store_baseline,
            charged_term_store_growth,
            progress,
        )?;
        if let Some(step) = step {
            unit_chain_memo.insert(premise, step);
        }
        if step.is_none() && std::env::var("AY_DT_DEBUG").is_ok() {
            eprintln!(
                "c context-premise-debug undischarged: {}",
                ay_proof::render_term_canonical(self.terms, premise)
            );
        }
        Ok(step)
    }

    /// The ground-encoding substitution bridge — see the call site above for
    /// the contract. `None` means no sealed instance + authored-equality
    /// combination explains the unit; every emitted step is re-validated by
    /// the strict whole-proof check (`forall_inst` substitution replay for
    /// the instance chain, the parallel-walk validator for the substitution
    /// lemma, authored-closure membership for each assumed equality).
    #[allow(clippy::too_many_arguments)]
    fn emit_ground_substituted_instance_unit(
        &mut self,
        proof: &mut Proof,
        unit: TermId,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        const MAX_BRIDGE_DERIVATIONS: usize = 32;
        let Some(derivation_map) = self.instance_derivations else {
            return Ok(None);
        };
        if derivation_map.is_empty() {
            return Ok(None);
        }
        // Authored defining equalities `(= key literal)`, keyed for the
        // occurs check. Both the equality TERM (for the assume and the lemma
        // literal) and the key are retained.
        let mut authored_equalities: Vec<(TermId, TermId)> = Vec::new();
        for &candidate in authored_terms.iter().chain(authored_conjuncts.iter()) {
            let TermData::App(symbol, args) = self.terms.get(candidate) else {
                continue;
            };
            if symbol.name() != "=" || args.len() != 2 {
                continue;
            }
            let (key, value) = (args[0], args[1]);
            if matches!(self.terms.get(value), TermData::Const(_))
                && !matches!(self.terms.get(key), TermData::Const(_))
                && !authored_equalities.iter().any(|&(eq, _)| eq == candidate)
            {
                authored_equalities.push((candidate, key));
            }
        }
        if authored_equalities.is_empty() {
            return Ok(None);
        }
        authored_equalities.sort_by_key(|&(eq, _)| eq.index());
        let mut derivations: Vec<FragmentInstanceDerivation> =
            derivation_map.values().cloned().collect();
        derivations.sort_by_key(|derivation| derivation.instance.index());
        for derivation in derivations.into_iter().take(MAX_BRIDGE_DERIVATIONS) {
            let instance = derivation.instance;
            if instance == unit {
                continue;
            }
            // Keys that occur in the instance — the validator's sharpness
            // requirement, checked with a bounded walk before any interning.
            let used: Vec<(TermId, TermId)> = authored_equalities
                .iter()
                .copied()
                .filter(|&(_, key)| Self::term_occurs_in(self.terms, key, instance))
                .collect();
            if used.is_empty() {
                continue;
            }
            // Decide BEFORE minting anything: the no-interning pre-check
            // guarantees the assembled clause passes the strict validator, so
            // a declined candidate leaves the term store untouched and the
            // growth meter exact.
            let pairs: Vec<(TermId, TermId)> = used
                .iter()
                .map(|&(equality, key)| {
                    let TermData::App(_, args) = self.terms.get(equality) else {
                        unreachable!("filtered to binary equalities above");
                    };
                    let _ = key;
                    (args[0], args[1])
                })
                .collect();
            if !ay_proof::ground_substitution_image_matches(self.terms, instance, unit, &pairs) {
                continue;
            }
            let (work, bytes) = Self::unit_chain_charge(used.len() + 3, 2 * used.len() + 4)?;
            progress(work, bytes)?;
            let mut lemma: Vec<TermId> = Vec::with_capacity(used.len() + 2);
            for &(equality, _) in &used {
                lemma.push(self.terms.mk_not_raw(equality));
            }
            lemma.push(self.terms.mk_not_raw(instance));
            lemma.push(unit);
            debug_assert!(ay_proof::recognize_ground_equality_substitution(
                self.terms, &lemma
            ));
            let instance_unit = Self::emit_forall_inst_unit_chain(
                self.terms,
                proof,
                &derivation,
                instance,
                progress,
            )?;
            let lemma_step = proof.add_step(ProofStep::TheoryLemma {
                theory: "EUF".to_owned(),
                clause: lemma.clone(),
                farkas: None,
                kind: TheoryLemmaKind::GroundEqualitySubstitution,
                lia: None,
            });
            let mut residual = lemma;
            let mut current = lemma_step;
            for &(equality, _) in &used {
                let assume_id = proof.add_assume(equality, None);
                let negated = self.terms.mk_not_raw(equality);
                residual.retain(|&literal| literal != negated);
                current = proof.add_resolution(residual.clone(), equality, current, assume_id);
            }
            let negated_instance = self.terms.mk_not_raw(instance);
            residual.retain(|&literal| literal != negated_instance);
            current = proof.add_resolution(residual.clone(), instance, current, instance_unit);
            if residual != [unit] {
                // Structural surprise (duplicate literals): decline rather
                // than hand the validator a mismatched resolution chain.
                return Ok(None);
            }
            self.reconcile_term_store_growth(
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )?;
            return Ok(Some(current));
        }
        Ok(None)
    }

    /// Bounded occurs check: whether `needle` occurs in `haystack`.
    fn term_occurs_in(terms: &TermStore, needle: TermId, haystack: TermId) -> bool {
        let mut stack = vec![haystack];
        let mut budget = 100_000usize;
        while let Some(current) = stack.pop() {
            if budget == 0 {
                return false;
            }
            budget -= 1;
            if current == needle {
                return true;
            }
            match terms.get(current) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }
}
