// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};
use ay_sat::ResolutionValidationError;

use super::types::OrFoldUnitPlan;
use super::ContextDerivationState;
use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};

/// Premise visits one entry may spend in a memo-backed fast pass.
const FAST_PASS_PREMISE_BUDGET: u64 = 20_000;
/// Premise visits one entry may spend in the memo-free deep-retry pass.
const DEEP_PASS_PREMISE_BUDGET: u64 = 400_000;

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

    /// Bound this entry's discharge search. Unbounded, one hard entry can
    /// spend the whole build deadline — the census then reports a resource
    /// abort rather than an authority verdict, which reads as success.
    fn reset_context_premise_budget(&mut self) {
        self.context_premise_budget = if self.context_deep_retry {
            DEEP_PASS_PREMISE_BUDGET
        } else {
            FAST_PASS_PREMISE_BUDGET
        };
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
        // clauses entailed only UNDER the problem's other constraints. The
        // sealed record only NAMES the premises; validity of the widened
        // clause is re-derived here by the bounded ground refuter and every
        // premise is discharged as an authored assumption, so nothing
        // producer-side is trusted.
        self.reset_context_premise_budget();
        let mut state = ContextDerivationState {
            authored_terms,
            authored_conjuncts,
            authored_bool_ites,
            unit_authority,
            unit_chain_memo,
            term_store_baseline,
            charged_term_store_growth,
            progress,
        };
        if let Some(step) = self.emit_context_derivation(proof, clause, &mut state)? {
            return Ok(step);
        }
        if let Some(step) = self.emit_context_synthesis(proof, clause, &mut state)? {
            return Ok(step);
        }
        if let Some(step) = self.emit_ground_substitution(proof, clause, &mut state)? {
            return Ok(step);
        }
        Err(self.unauthenticated_original_clause_error(clause_id, clause))
    }

    fn unauthenticated_original_clause_error(
        &self,
        clause_id: u64,
        clause: &[TermId],
    ) -> ExactOriginalProofError {
        // The clause shape distinguishes a missing authority lane from a
        // producer defect; disclosure remains behind the typed probe flag.
        self.report_unauthenticated_original_clause(clause_id, clause);
        ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id,
            clause: Self::normalize_clause(clause),
        }
    }

    fn report_unauthenticated_original_clause(&self, clause_id: u64, clause: &[TermId]) {
        if !ay_core::misc_cli_flags().probe_cert_reject {
            return;
        }
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
}
