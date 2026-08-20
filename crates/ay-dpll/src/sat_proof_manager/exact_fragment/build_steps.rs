// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};
use ay_sat::ResolutionValidationError;

use super::types::OrFoldUnitPlan;
use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};

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
        unit_authority: bool,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if authored_terms.contains(&unit) || (unit_authority && authored_conjuncts.contains(&unit))
        {
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
                // c7 (#ppp-c7): sealed PropagateValues replay, possibly
                // rooted in a sealed qpf premise-forced instance. Memoized
                // per distinct unit; declines fall through fail-closed.
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
                // Last resort before refusal: a packed clausification unit
                // whose flattened disjuncts contain a complementary pair (or
                // one of the `and_pos`/`or_neg` gate shapes) is a
                // propositional TAUTOLOGY — true regardless of provenance, so
                // it needs no pedigree back to an authored assertion at all.
                // The canonical producer is ite/store clausification emitting
                // `(or (or .. P) (not P))` unannotated (the QF_AUFLIRA ROW
                // envelope red, 2026-08-19). The recognizer IS the strict
                // validator for `BoolTautology`, so the whole-proof re-check
                // re-derives exactly what is admitted here; a wrong guess
                // fails authentication exactly like today's refusal. Placed
                // after every pedigree lane so it only ever runs on units
                // that would otherwise hard-fail.
                if ay_proof::recognize_bool_tautology(self.terms, &[*unit]) {
                    let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                    progress(work, bytes)?;
                    return Ok(proof.add_step(ProofStep::TheoryLemma {
                        theory: "bool".to_owned(),
                        clause: vec![*unit],
                        farkas: None,
                        kind: TheoryLemmaKind::BoolTautology,
                        lia: None,
                    }));
                }
                // Its arithmetic sibling: the negated unit (or-packed
                // literals flattened conjunctively) is an infeasible linear
                // system — again intrinsically valid, no pedigree needed.
                if ay_proof::recognize_arith_clause_tautology(self.terms, &[*unit]) {
                    let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                    progress(work, bytes)?;
                    return Ok(proof.add_step(ProofStep::TheoryLemma {
                        theory: "arith".to_owned(),
                        clause: vec![*unit],
                        farkas: None,
                        kind: TheoryLemmaKind::ArithClauseTautology,
                        lia: None,
                    }));
                }
                // Term-ite branch projection and guarded ROW expansion: the
                // pedigree-free shapes ite/store clausification emits.
                if ay_proof::recognize_ite_branch_projection(self.terms, &[*unit]) {
                    let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                    progress(work, bytes)?;
                    return Ok(proof.add_step(ProofStep::TheoryLemma {
                        theory: "ite".to_owned(),
                        clause: vec![*unit],
                        farkas: None,
                        kind: TheoryLemmaKind::IteBranchProjection,
                        lia: None,
                    }));
                }
                // Or-packed EUF congruence/transitivity chains — the
                // extensionality-instance and explanation shapes.
                if ay_proof::recognize_euf_congruent(self.terms, &[*unit])
                    || ay_proof::recognize_euf_transitive(self.terms, &[*unit])
                {
                    let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                    progress(work, bytes)?;
                    let kind = if ay_proof::recognize_euf_congruent(self.terms, &[*unit]) {
                        TheoryLemmaKind::EufCongruent
                    } else {
                        TheoryLemmaKind::EufTransitive
                    };
                    return Ok(proof.add_step(ProofStep::TheoryLemma {
                        theory: "EUF".to_owned(),
                        clause: vec![*unit],
                        farkas: None,
                        kind,
                        lia: None,
                    }));
                }
                if ay_proof::recognize_array_guarded_row_expansion(self.terms, &[*unit]) {
                    let (work, bytes) = Self::unit_chain_charge(1, 1)?;
                    progress(work, bytes)?;
                    return Ok(proof.add_step(ProofStep::TheoryLemma {
                        theory: "array".to_owned(),
                        clause: vec![*unit],
                        farkas: None,
                        kind: TheoryLemmaKind::ArrayGuardedRowExpansion,
                        lia: None,
                    }));
                }
            }
        }
        // A NON-UNIT original clause that is a propositional clausification
        // tautology (`(cl (not (or A B)) A B)` — the or_pos shape emitted as
        // a plain original clause) needs no pedigree either; same contract as
        // the unit lanes above, same strict re-validation downstream.
        if clause.len() >= 2 && ay_proof::recognize_bool_tautology(self.terms, clause) {
            let (work, bytes) = Self::unit_chain_charge(1, clause.len())?;
            progress(work, bytes)?;
            return Ok(proof.add_step(ProofStep::TheoryLemma {
                theory: "bool".to_owned(),
                clause: clause.to_vec(),
                farkas: None,
                kind: TheoryLemmaKind::BoolTautology,
                lia: None,
            }));
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
        }
        Err(ExactOriginalProofError::UnauthenticatedOriginalClause {
            clause_id,
            clause: Self::normalize_clause(clause),
        })
    }
}
