// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact replay for ground equalities substituted through quantifier instances.

use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TermStore, TheoryLemmaKind};
use ay_sat::ResolutionValidationError;

use super::ContextDerivationState;
use crate::sat_proof_manager::{
    ExactOriginalProofError, FragmentInstanceDerivation, SatProofManager,
};

const MAX_BRIDGE_DERIVATIONS: usize = 32;

struct GroundSubstitutionState<'a> {
    proof: &'a mut Proof,
    unit: TermId,
    authored_equalities: Vec<(TermId, TermId)>,
    term_store_baseline: usize,
    charged_term_store_growth: &'a mut usize,
    progress: &'a mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
}

enum GroundSubstitutionAttempt {
    Continue,
    Emitted(ProofId),
    Abort,
}

impl SatProofManager<'_> {
    /// Rebuild a sealed instance after applying authored defining equalities.
    ///
    /// Every emitted step is independently revalidated: `forall_inst`
    /// replays the instance, the strict parallel-walk lemma validates the
    /// substitution, and each defining equality is an authored assumption.
    pub(super) fn emit_ground_substitution(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let [unit] = clause else {
            return Ok(None);
        };
        if ay_core::misc_cli_flags().probe_cert_reject {
            ay_core::safe_eprintln!(
                "--probe-cert-reject: gs-bridge entry: derivations={} authored_terms={} conjuncts={}",
                self.instance_derivations.map_or(0, |map| map.len()),
                state.authored_terms.len(),
                state.authored_conjuncts.len(),
            );
        }
        let authored_equalities =
            self.authored_ground_equalities(state.authored_terms, state.authored_conjuncts);
        if authored_equalities.is_empty() {
            return Ok(None);
        }
        let authored_terms = state.authored_terms;
        let authored_conjuncts = state.authored_conjuncts;
        let mut derivations: Vec<FragmentInstanceDerivation> = self
            .instance_derivations
            .map(|map| map.values().cloned().collect())
            .unwrap_or_default();
        derivations.sort_by_key(|derivation| derivation.instance.index());
        let mut state = GroundSubstitutionState {
            proof,
            unit: *unit,
            authored_equalities,
            term_store_baseline: state.term_store_baseline,
            charged_term_store_growth: state.charged_term_store_growth,
            progress: state.progress,
        };
        for derivation in derivations.into_iter().take(MAX_BRIDGE_DERIVATIONS) {
            match self.emit_ground_substitution_derivation(&derivation, &mut state)? {
                GroundSubstitutionAttempt::Continue => {}
                GroundSubstitutionAttempt::Emitted(step) => return Ok(Some(step)),
                GroundSubstitutionAttempt::Abort => return Ok(None),
            }
        }
        self.emit_ground_substitution_authored_source(
            &mut state,
            authored_terms,
            authored_conjuncts,
        )
    }

    fn authored_ground_equalities(
        &self,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> Vec<(TermId, TermId)> {
        let mut equalities = Vec::new();
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
                && !equalities
                    .iter()
                    .any(|&(equality, _)| equality == candidate)
            {
                equalities.push((candidate, key));
            }
        }
        equalities.sort_by_key(|&(equality, _)| equality.index());
        equalities
    }

    fn emit_ground_substitution_derivation(
        &mut self,
        derivation: &FragmentInstanceDerivation,
        state: &mut GroundSubstitutionState<'_>,
    ) -> Result<GroundSubstitutionAttempt, ExactOriginalProofError> {
        let instance = derivation.instance;
        if instance == state.unit {
            return Ok(GroundSubstitutionAttempt::Continue);
        }
        if ay_core::misc_cli_flags().probe_cert_reject {
            ay_core::safe_eprintln!(
                "--probe-cert-reject: gs-bridge candidate instance={} unit={}",
                ay_proof::render_term_canonical(self.terms, instance),
                ay_proof::render_term_canonical(self.terms, state.unit),
            );
        }
        let used: Vec<(TermId, TermId)> = state
            .authored_equalities
            .iter()
            .copied()
            .filter(|&(_, key)| Self::term_occurs_in(self.terms, key, instance))
            .collect();
        if used.is_empty() {
            if ay_core::misc_cli_flags().probe_cert_reject {
                ay_core::safe_eprintln!(
                    "--probe-cert-reject: gs-bridge DECLINED (no equality key occurs; {} authored eqs)",
                    state.authored_equalities.len(),
                );
            }
            return Ok(GroundSubstitutionAttempt::Continue);
        }
        let Some(pairs) = self.ground_equality_pairs(&used) else {
            return Ok(GroundSubstitutionAttempt::Continue);
        };
        if !ay_proof::ground_substitution_image_matches(self.terms, instance, state.unit, &pairs) {
            if ay_core::misc_cli_flags().probe_cert_reject {
                ay_core::safe_eprintln!(
                    "--probe-cert-reject: gs-bridge DECLINED (image mismatch) pairs={}",
                    pairs.len(),
                );
            }
            return Ok(GroundSubstitutionAttempt::Continue);
        }
        let (work, bytes) = Self::unit_chain_charge(used.len() + 3, 2 * used.len() + 4)?;
        (state.progress)(work, bytes)?;
        let mut lemma: Vec<TermId> = used
            .iter()
            .map(|&(equality, _)| self.terms.mk_not_raw(equality))
            .collect();
        lemma.push(self.terms.mk_not_raw(instance));
        lemma.push(state.unit);
        debug_assert!(ay_proof::recognize_ground_equality_substitution(
            self.terms, &lemma
        ));
        let instance_unit = Self::emit_forall_inst_unit_chain(
            self.terms,
            state.proof,
            derivation,
            instance,
            state.progress,
        )?;
        let mut current = state.proof.add_step(ProofStep::TheoryLemma {
            theory: "EUF".to_owned(),
            clause: lemma.clone(),
            farkas: None,
            kind: TheoryLemmaKind::GroundEqualitySubstitution,
            lia: None,
        });
        let mut residual = lemma;
        for &(equality, _) in &used {
            let assume_id = state.proof.add_assume(equality, None);
            let negated = self.terms.mk_not_raw(equality);
            residual.retain(|&literal| literal != negated);
            current = state
                .proof
                .add_resolution(residual.clone(), equality, current, assume_id);
        }
        let negated_instance = self.terms.mk_not_raw(instance);
        residual.retain(|&literal| literal != negated_instance);
        current = state
            .proof
            .add_resolution(residual.clone(), instance, current, instance_unit);
        if residual != [state.unit] {
            return Ok(GroundSubstitutionAttempt::Abort);
        }
        self.reconcile_term_store_growth(
            state.term_store_baseline,
            state.charged_term_store_growth,
            state.progress,
        )?;
        Ok(GroundSubstitutionAttempt::Emitted(current))
    }

    /// Replay a normalized substitution whose source is an authored root or
    /// conjunct rather than a recorded quantifier instance.
    fn emit_ground_substitution_authored_source(
        &mut self,
        state: &mut GroundSubstitutionState<'_>,
        authored_terms: &ay_core::kani_compat::DetHashSet<TermId>,
        authored_conjuncts: &ay_core::kani_compat::DetHashSet<TermId>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        const MAX_BRIDGE_SOURCES: usize = 64;
        let mut sources: Vec<TermId> = authored_terms
            .iter()
            .chain(authored_conjuncts.iter())
            .copied()
            .collect();
        sources.sort_by_key(|term| term.index());
        sources.dedup();
        for source in sources.into_iter().take(MAX_BRIDGE_SOURCES) {
            if source == state.unit {
                continue;
            }
            let used: Vec<(TermId, TermId)> = state
                .authored_equalities
                .iter()
                .copied()
                .filter(|&(equality, key)| {
                    equality != source && Self::term_occurs_in(self.terms, key, source)
                })
                .collect();
            if used.is_empty() {
                continue;
            }
            let Some(pairs) = self.ground_equality_pairs(&used) else {
                continue;
            };
            if !ay_proof::ground_substitution_image_matches(self.terms, source, state.unit, &pairs)
            {
                if ay_core::misc_cli_flags().probe_cert_reject {
                    ay_core::safe_eprintln!(
                        "--probe-cert-reject: gs-bridge authored-source DECLINED pairs={} source={} UNIT={}",
                        pairs.len(),
                        ay_proof::render_term_canonical(self.terms, source),
                        ay_proof::render_term_canonical(self.terms, state.unit),
                    );
                }
                continue;
            }
            let (work, bytes) = Self::unit_chain_charge(used.len() + 3, 2 * used.len() + 4)?;
            (state.progress)(work, bytes)?;
            let source_assume = state.proof.add_assume(source, None);
            let mut lemma: Vec<TermId> = used
                .iter()
                .map(|&(equality, _)| self.terms.mk_not_raw(equality))
                .collect();
            lemma.push(self.terms.mk_not_raw(source));
            lemma.push(state.unit);
            debug_assert!(ay_proof::recognize_ground_equality_substitution(
                self.terms, &lemma
            ));
            let mut current = state.proof.add_step(ProofStep::TheoryLemma {
                theory: "EUF".to_owned(),
                clause: lemma.clone(),
                farkas: None,
                kind: TheoryLemmaKind::GroundEqualitySubstitution,
                lia: None,
            });
            let mut residual = lemma;
            for &(equality, _) in &used {
                let assume_id = state.proof.add_assume(equality, None);
                let negated = self.terms.mk_not_raw(equality);
                residual.retain(|&literal| literal != negated);
                current =
                    state
                        .proof
                        .add_resolution(residual.clone(), equality, current, assume_id);
            }
            let negated_source = self.terms.mk_not_raw(source);
            residual.retain(|&literal| literal != negated_source);
            current = state
                .proof
                .add_resolution(residual.clone(), source, current, source_assume);
            if residual != [state.unit] {
                return Ok(None);
            }
            self.reconcile_term_store_growth(
                state.term_store_baseline,
                state.charged_term_store_growth,
                state.progress,
            )?;
            return Ok(Some(current));
        }
        Ok(None)
    }

    fn ground_equality_pairs(&self, used: &[(TermId, TermId)]) -> Option<Vec<(TermId, TermId)>> {
        used.iter()
            .map(|&(equality, _)| match self.terms.get(equality) {
                TermData::App(_, args) if args.len() == 2 => Some((args[0], args[1])),
                _ => None,
            })
            .collect()
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
                TermData::Ite(condition, then_term, else_term) => {
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                _ => {}
            }
        }
        false
    }
}
