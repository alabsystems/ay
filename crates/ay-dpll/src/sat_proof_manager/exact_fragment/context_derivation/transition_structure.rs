// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified transition-structure bridges for context-derived premises.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TheoryLemmaKind};

use super::ContextDerivationState;
use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};
use crate::theory_inference::DatatypeRegistries;

impl SatProofManager<'_> {
    pub(super) fn emit_context_transition_structure(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        state: &mut ContextDerivationState<'_>,
        depth: usize,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let Some(registry) = self.dt_registry_data else {
            return Ok(None);
        };
        let view = DatatypeRegistries::from_data(registry);
        if let Some(step) =
            self.emit_synthesized_tester_bridge(proof, premise, state, depth, &view)?
        {
            return Ok(Some(step));
        }
        self.emit_equality_neighbor_bridge(proof, premise, state, depth, &view)
    }

    fn emit_synthesized_tester_bridge(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        state: &mut ContextDerivationState<'_>,
        depth: usize,
        view: &DatatypeRegistries<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let subjects = datatype_sorted_subjects(self.terms, premise, view.datatypes);
        for subject in subjects {
            let Some(datatype) = datatype_of_sort(self.terms.sort(subject), view.datatypes) else {
                continue;
            };
            let constructors = view
                .datatypes
                .iter()
                .find(|(name, _)| name == datatype)
                .map(|(_, constructors)| constructors.clone())
                .unwrap_or_default();
            for constructor in constructors {
                let tester = self.terms.mk_app(
                    ay_core::Symbol::named(format!("is-{constructor}")),
                    vec![subject],
                    ay_core::Sort::Bool,
                );
                if tester == premise {
                    // `P ∨ ¬P` is refuter-valid but cannot establish `P`;
                    // recursing through that self-bridge only burns depth.
                    continue;
                }
                let not_tester = self.terms.mk_not(tester);
                self.reconcile_term_store_growth(
                    state.term_store_baseline,
                    state.charged_term_store_growth,
                    state.progress,
                )?;
                if !self.context_refuter_accepts(
                    &[premise, not_tester],
                    view.datatypes,
                    view.ctor_selectors,
                ) {
                    continue;
                }
                let Some(tester_step) =
                    self.emit_context_premise_step(proof, tester, state, depth - 1)?
                else {
                    continue;
                };
                let (work, bytes) = Self::unit_chain_charge(2, 2)?;
                (state.progress)(work, bytes)?;
                let bridge = proof.add_step(ProofStep::TheoryLemma {
                    theory: "dt".to_owned(),
                    clause: vec![premise, not_tester],
                    farkas: None,
                    kind: TheoryLemmaKind::DatatypeGroundConflict,
                    lia: None,
                });
                return Ok(Some(proof.add_resolution(
                    vec![premise],
                    tester,
                    bridge,
                    tester_step,
                )));
            }
        }
        Ok(None)
    }

    fn emit_equality_neighbor_bridge(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        state: &mut ContextDerivationState<'_>,
        depth: usize,
        view: &DatatypeRegistries<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let subjects = datatype_sorted_subjects(self.terms, premise, view.datatypes);
        let candidates = self.equality_neighbor_candidates(&subjects);
        for candidate in candidates {
            if let Some(step) = self
                .emit_equality_neighbor_candidate(proof, premise, candidate, state, depth, view)?
            {
                return Ok(Some(step));
            }
        }
        Ok(None)
    }

    /// Index every sealed single-equality by each of its sides, once per
    /// build. The scan this replaces ran over every key on every premise
    /// visit, and the memo-free retry pass makes thousands of those.
    fn ensure_equality_neighbour_index(&mut self) {
        if self.equality_neighbour_index.is_some() {
            return;
        }
        let mut index: HashMap<TermId, Vec<(usize, TermId, TermId)>> = HashMap::default();
        if let Some(derivations) = self.context_derivations {
            for (rank, key) in derivations.keys().enumerate() {
                let [equality] = key.as_slice() else {
                    continue;
                };
                let TermData::App(symbol, args) = self.terms.get(*equality) else {
                    continue;
                };
                if symbol.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (first, second) = (args[0], args[1]);
                index
                    .entry(first)
                    .or_default()
                    .push((rank, *equality, second));
                index
                    .entry(second)
                    .or_default()
                    .push((rank, *equality, first));
            }
        }
        self.equality_neighbour_index = Some(index);
    }

    fn equality_neighbor_candidates(
        &mut self,
        subjects: &[TermId],
    ) -> Vec<(TermId, TermId, TermId)> {
        if self.context_derivations.is_none() {
            return Vec::new();
        }
        self.ensure_equality_neighbour_index();
        let Some(index) = self.equality_neighbour_index.as_ref() else {
            return Vec::new();
        };
        // Rebuild the former key-major scan's ORDER exactly: candidates
        // sorted by (key rank, subject position), then whole key groups
        // admitted until the 64 mark is passed — the scan's own stopping
        // rule. Order is load-bearing: the caller takes the first candidate
        // that discharges, so a different order reaches different
        // derivations, which a speedup may not change.
        let mut ranked: Vec<(usize, usize, TermId, TermId, TermId)> = Vec::new();
        for (position, &subject) in subjects.iter().enumerate() {
            let Some(neighbours) = index.get(&subject) else {
                continue;
            };
            for &(rank, equality, neighbor) in neighbours {
                ranked.push((rank, position, equality, subject, neighbor));
            }
        }
        ranked.sort_unstable();
        let mut candidates = Vec::new();
        let mut group = usize::MAX;
        for (rank, _, equality, subject, neighbor) in ranked {
            if rank != group && candidates.len() >= 64 {
                break;
            }
            group = rank;
            candidates.push((equality, subject, neighbor));
        }
        candidates
    }

    fn emit_equality_neighbor_candidate(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        candidate: (TermId, TermId, TermId),
        state: &mut ContextDerivationState<'_>,
        depth: usize,
        view: &DatatypeRegistries<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let (equality, subject, neighbor) = candidate;
        let Some(transported) = self.transport_premise_shape(premise, subject, neighbor) else {
            return Ok(None);
        };
        let not_equality = self.terms.mk_not(equality);
        let not_transported = match self.terms.get(transported) {
            TermData::Not(inner) => *inner,
            _ => self.terms.mk_not(transported),
        };
        self.reconcile_term_store_growth(
            state.term_store_baseline,
            state.charged_term_store_growth,
            state.progress,
        )?;
        let widened = vec![premise, not_equality, not_transported];
        if !self.context_refuter_accepts(&widened, view.datatypes, view.ctor_selectors) {
            return Ok(None);
        }
        let Some(equality_step) =
            self.emit_context_premise_step(proof, equality, state, depth - 1)?
        else {
            return Ok(None);
        };
        let Some(transported_step) =
            self.emit_context_premise_step(proof, transported, state, depth - 1)?
        else {
            return Ok(None);
        };
        let (work, bytes) = Self::unit_chain_charge(3, 3)?;
        (state.progress)(work, bytes)?;
        let lemma = proof.add_step(ProofStep::TheoryLemma {
            theory: "dt".to_owned(),
            clause: widened.clone(),
            farkas: None,
            kind: TheoryLemmaKind::DatatypeGroundConflict,
            lia: None,
        });
        let middle = proof.add_resolution(
            vec![premise, not_transported],
            equality,
            lemma,
            equality_step,
        );
        let transported_pivot = match self.terms.get(transported) {
            TermData::Not(inner) => *inner,
            _ => transported,
        };
        Ok(Some(proof.add_resolution(
            vec![premise],
            transported_pivot,
            middle,
            transported_step,
        )))
    }

    fn transport_premise_shape(
        &mut self,
        premise: TermId,
        subject: TermId,
        neighbor: TermId,
    ) -> Option<TermId> {
        match self.terms.get(premise).clone() {
            TermData::App(ay_core::Symbol::Named(name), args)
                if args.as_slice() == [subject] && name.starts_with("is-") =>
            {
                Some(self.terms.mk_app(
                    ay_core::Symbol::named(name),
                    vec![neighbor],
                    ay_core::Sort::Bool,
                ))
            }
            TermData::Not(inner) => {
                let TermData::App(symbol, args) = self.terms.get(inner).clone() else {
                    return None;
                };
                if symbol.name() != "=" || args.len() != 2 {
                    return None;
                }
                let other = if args[0] == subject {
                    args[1]
                } else if args[1] == subject {
                    args[0]
                } else {
                    return None;
                };
                if self.terms.sort(other) != self.terms.sort(neighbor) {
                    return None;
                }
                let transported_equality = self.terms.mk_eq(other, neighbor);
                Some(self.terms.mk_not(transported_equality))
            }
            _ => None,
        }
    }
}

pub(super) fn datatype_sorted_subjects(
    terms: &ay_core::TermStore,
    term: TermId,
    datatypes: &[(String, Vec<String>)],
) -> Vec<TermId> {
    let mut subjects = Vec::new();
    let mut pending = vec![term];
    let mut visited = ay_core::kani_compat::DetHashSet::default();
    while let Some(current) = pending.pop() {
        if !visited.insert(current) || visited.len() > 64 {
            continue;
        }
        let constructor_headed = match terms.get(current) {
            TermData::Var(name, _) => datatypes
                .iter()
                .any(|(_, constructors)| constructors.iter().any(|item| item == name)),
            TermData::App(symbol, _) => datatypes
                .iter()
                .any(|(_, constructors)| constructors.iter().any(|item| item == symbol.name())),
            _ => false,
        };
        if !constructor_headed
            && datatype_of_sort(terms.sort(current), datatypes).is_some()
            && !subjects.contains(&current)
        {
            subjects.push(current);
        }
        match terms.get(current) {
            TermData::App(_, arguments) => pending.extend(arguments.iter().copied()),
            TermData::Not(inner) => pending.push(*inner),
            _ => {}
        }
    }
    subjects
}

pub(super) fn datatype_of_sort<'d>(
    sort: &ay_core::Sort,
    datatypes: &'d [(String, Vec<String>)],
) -> Option<&'d str> {
    let name = match sort {
        ay_core::Sort::Uninterpreted(name) => name.as_str(),
        ay_core::Sort::Datatype(definition) => definition.name.as_str(),
        _ => return None,
    };
    datatypes
        .iter()
        .find(|(datatype, _)| datatype == name)
        .map(|(datatype, _)| datatype.as_str())
}
