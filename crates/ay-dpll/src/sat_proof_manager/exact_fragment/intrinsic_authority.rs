// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pedigree-free exact-fragment clauses authenticated by strict recognizers.

use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TheoryLemmaKind};
use ay_sat::ResolutionValidationError;

use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};

impl SatProofManager<'_> {
    pub(super) fn emit_intrinsic_original_unit(
        &mut self,
        proof: &mut Proof,
        unit: TermId,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let Some((theory, kind)) = self.recognize_intrinsic_original_unit(unit) else {
            return Ok(None);
        };
        let (work, bytes) = Self::unit_chain_charge(1, 1)?;
        progress(work, bytes)?;
        Ok(Some(proof.add_step(ProofStep::TheoryLemma {
            theory: theory.to_owned(),
            clause: vec![unit],
            farkas: None,
            kind,
            lia: None,
        })))
    }

    fn recognize_intrinsic_original_unit(
        &self,
        unit: TermId,
    ) -> Option<(&'static str, TheoryLemmaKind)> {
        let clause = [unit];
        if ay_proof::recognize_bool_tautology(self.terms, &clause) {
            return Some(("bool", TheoryLemmaKind::BoolTautology));
        }
        if ay_proof::recognize_arith_clause_tautology(self.terms, &clause) {
            return Some(("arith", TheoryLemmaKind::ArithClauseTautology));
        }
        if ay_proof::recognize_ite_branch_projection(self.terms, &clause) {
            return Some(("ite", TheoryLemmaKind::IteBranchProjection));
        }
        if ay_proof::recognize_euf_congruent(self.terms, &clause) {
            return Some(("EUF", TheoryLemmaKind::EufCongruent));
        }
        if ay_proof::recognize_euf_transitive(self.terms, &clause) {
            return Some(("EUF", TheoryLemmaKind::EufTransitive));
        }
        if ay_proof::recognize_array_guarded_row_expansion(self.terms, &clause) {
            return Some(("array", TheoryLemmaKind::ArrayGuardedRowExpansion));
        }
        // Only Bool-indexed finite carriers are available without the typed
        // datatype registry. The shared recognizer rejects incomplete,
        // duplicated, foreign-array, and ill-sorted branch sets.
        ay_proof::recognize_array_finite_select_expansion(self.terms, &clause)
            .then_some(("array", TheoryLemmaKind::ArrayFiniteSelectExpansion))
    }

    pub(super) fn emit_intrinsic_original_clause(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if clause.len() >= 2 && ay_proof::recognize_bool_tautology(self.terms, clause) {
            let (work, bytes) = Self::unit_chain_charge(1, clause.len())?;
            progress(work, bytes)?;
            return Ok(Some(Self::add_intrinsic_original_clause(
                proof,
                "bool",
                clause.to_vec(),
                TheoryLemmaKind::BoolTautology,
            )));
        }
        // Mid-solve DT/EUF conflict clauses have no annotation channel to the
        // indexed ledgers. Re-derive their validity directly from the clause
        // and datatype registries through the same bounded recognizer used by
        // the strict checker. A missing registry or rejected shape falls
        // through without authority. Keep this after the pre-existing Boolean
        // recognizer and before the direct-EUF recognizer to preserve their
        // authority ordering across the integration.
        if let Some(registry) = self.dt_registry_data {
            let view = crate::theory_inference::DatatypeRegistries::from_data(registry);
            if let Some(kind) =
                crate::theory_inference::infer_dt_lemma_kind(self.terms, clause, &view)
            {
                let (work, bytes) = Self::unit_chain_charge(clause.len(), clause.len())?;
                progress(work, bytes)?;
                return Ok(Some(Self::add_intrinsic_original_clause(
                    proof,
                    "dt",
                    clause.to_vec(),
                    kind,
                )));
            }
        }
        if clause.len() < 2 {
            return Ok(None);
        }
        let Some(validator_clause) = self.direct_euf_validator_clause(clause) else {
            return Ok(None);
        };
        let (work, bytes) = Self::unit_chain_charge(1, clause.len())?;
        progress(work, bytes)?;
        let kind = if ay_proof::recognize_euf_transitive(self.terms, &validator_clause) {
            Some(TheoryLemmaKind::EufTransitive)
        } else if ay_proof::recognize_euf_congruent(self.terms, &validator_clause) {
            Some(TheoryLemmaKind::EufCongruent)
        } else {
            None
        };
        Ok(kind
            .map(|kind| Self::add_intrinsic_original_clause(proof, "EUF", validator_clause, kind)))
    }

    /// Put the unique positive conclusion last, as the strict EUF validators
    /// require. Exact normalized-clause binding is checked by the caller.
    fn direct_euf_validator_clause(&self, clause: &[TermId]) -> Option<Vec<TermId>> {
        let mut conclusion_index = None;
        for (index, &literal) in clause.iter().enumerate() {
            let mut current = literal;
            let mut negated = false;
            while let TermData::Not(inner) = self.terms.get(current) {
                current = *inner;
                negated = !negated;
            }
            if !negated && conclusion_index.replace(index).is_some() {
                return None;
            }
        }
        let conclusion_index = conclusion_index?;
        let mut validator_clause = Vec::with_capacity(clause.len());
        validator_clause.extend(
            clause
                .iter()
                .enumerate()
                .filter_map(|(index, &literal)| (index != conclusion_index).then_some(literal)),
        );
        validator_clause.push(clause[conclusion_index]);
        Some(validator_clause)
    }

    fn add_intrinsic_original_clause(
        proof: &mut Proof,
        theory: &str,
        clause: Vec<TermId>,
        kind: TheoryLemmaKind,
    ) -> ProofId {
        proof.add_step(ProofStep::TheoryLemma {
            theory: theory.to_owned(),
            clause,
            farkas: None,
            kind,
            lia: None,
        })
    }
}
