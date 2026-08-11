// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact support-to-`true` transfer between authenticated flat-AND ORs.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::super::proof_surface_syntax::strip_frontend_annotations;
use super::super::proof_trust_surgery_provenance::{
    retained_original_rows_are_signable, source_set_is_exactly_authored,
    surface_is_direct_arithmetic_literal_prechecked, unique_atoms, OriginalSourceIndex,
    SurgeryPlanningBudget, MAX_PROVENANCE_REPAIR_TERMS,
};
use super::super::proof_trust_surgery_surface_audit::ProvenanceSurfaceAudit;
use super::super::Executor;
use super::and_conflict::{
    authenticate_flat_and_or_surface_prechecked, exact_term_permutation,
    MAX_CONJUNCTIVE_SOURCE_TERMS,
};
use super::ProvenanceOrAndRefutation;

#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_transfer_boundary_tests.rs"]
mod boundary_tests;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_transfer_carcara_tests.rs"]
mod carcara_tests;
#[path = "proof_trust_surgery_provenance_or_and_transfer_emit.rs"]
mod emit;
#[path = "proof_trust_surgery_provenance_or_and_transfer_shape.rs"]
mod shape;
#[path = "proof_trust_surgery_provenance_or_and_transfer_surface.rs"]
mod surface;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_transfer_tests.rs"]
mod tests;
#[path = "proof_trust_surgery_provenance_or_and_transfer_volume.rs"]
mod volume;

pub(super) const MAX_CONJUNCTIVE_TRANSFER_PROJECTIONS: usize = 512;

pub(in crate::executor::proof_repair) struct ProvenanceOrAndTransferPlan {
    pub(super) goal: TermId,
    pub(super) orig: TermId,
    pub(super) source_disjuncts: Vec<TermId>,
    pub(super) target_disjuncts: Vec<TermId>,
    pub(super) remaining_targets: Vec<TermId>,
    pub(super) authored_sources: Vec<TermId>,
    pub(super) outcomes: Vec<ProvenanceOrAndTransferOutcome>,
}

fn remaining_target_set(
    source_disjuncts: &[TermId],
    outcomes: &[ProvenanceOrAndTransferOutcome],
) -> Option<Vec<TermId>> {
    let mut remaining: HashSet<TermId> = source_disjuncts.iter().copied().collect();
    if remaining.len() != source_disjuncts.len() {
        return None;
    }
    for outcome in outcomes {
        if !remaining.remove(&outcome.source()) {
            return None;
        }
        if let ProvenanceOrAndTransferOutcome::Map(mapping) = outcome {
            remaining.insert(mapping.target);
        }
    }
    let mut remaining: Vec<_> = remaining.into_iter().collect();
    remaining.sort_unstable();
    Some(remaining)
}

pub(super) enum ProvenanceOrAndTransferOutcome {
    Refute(ProvenanceOrAndRefutation),
    Map(ProvenanceOrAndMapping),
}

impl ProvenanceOrAndTransferOutcome {
    pub(super) fn source(&self) -> TermId {
        match self {
            Self::Refute(refutation) => refutation.disjunct,
            Self::Map(mapping) => mapping.source,
        }
    }
}

pub(super) struct ProvenanceOrAndMapping {
    pub(super) source: TermId,
    pub(super) target: TermId,
    pub(super) target_children: Vec<TermId>,
    pub(super) projections: Vec<ProvenanceOrAndProjection>,
    pub(super) has_true: bool,
}

pub(super) struct ProvenanceOrAndProjection {
    pub(super) index: u32,
    pub(super) conjunct: TermId,
}

impl ProvenanceOrAndTransferPlan {
    pub(super) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        surface::protect_surface_operands(self, audit, terms);
    }
}

fn is_bool_value(terms: &ay_core::TermStore, term: TermId, value: bool) -> bool {
    matches!(terms.get(term), TermData::Const(Constant::Bool(actual)) if *actual == value)
}

fn flat_bool_and_children(
    terms: &ay_core::TermStore,
    term: TermId,
    allow_duplicates: bool,
) -> Option<Vec<TermId>> {
    let TermData::App(Symbol::Named(head), children) = terms.get(term) else {
        return None;
    };
    if head != "and"
        || *terms.sort(term) != Sort::Bool
        || !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&children.len())
        || children.iter().any(|&child| {
            *terms.sort(child) != Sort::Bool
                || matches!(terms.get(child), TermData::App(Symbol::Named(head), _) if head == "and")
        })
        || !allow_duplicates && !unique_atoms(terms, children)
    {
        return None;
    }
    Some(children.clone())
}

fn target_and_branches(
    terms: &ay_core::TermStore,
    goal: TermId,
) -> Option<(Vec<TermId>, Vec<(TermId, Vec<TermId>)>)> {
    let TermData::App(Symbol::Named(head), disjuncts) = terms.get(goal) else {
        return None;
    };
    if head != "or"
        || *terms.sort(goal) != Sort::Bool
        || !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
        || !unique_atoms(terms, disjuncts)
    {
        return None;
    }
    let mut total = 0usize;
    let mut branches = Vec::with_capacity(disjuncts.len());
    for &disjunct in disjuncts {
        let children = flat_bool_and_children(terms, disjunct, true)?;
        total = total.checked_add(children.len())?;
        if total > MAX_CONJUNCTIVE_SOURCE_TERMS {
            return None;
        }
        branches.push((disjunct, children));
    }
    Some((disjuncts.clone(), branches))
}

fn expected_target_children(
    terms: &mut ay_core::TermStore,
    source: &[TermId],
    supports: &HashSet<TermId>,
) -> Vec<TermId> {
    let truth = terms.mk_bool(true);
    source
        .iter()
        .map(|child| {
            if supports.contains(child) {
                truth
            } else {
                *child
            }
        })
        .collect()
}

fn mapping_for_target(
    terms: &mut ay_core::TermStore,
    source: TermId,
    source_children: &[TermId],
    target: TermId,
    target_children: &[TermId],
    supports: &HashSet<TermId>,
) -> Option<ProvenanceOrAndMapping> {
    if source_children.len() != target_children.len()
        || source_children
            .iter()
            .chain(target_children)
            .any(|&child| is_bool_value(terms, child, false))
    {
        return None;
    }
    let expected = expected_target_children(terms, source_children, supports);
    if !exact_term_permutation(&expected, target_children) {
        return None;
    }
    let mut projections = Vec::new();
    let mut projected = HashSet::default();
    let mut has_true = false;
    for &conjunct in target_children {
        if is_bool_value(terms, conjunct, true) {
            has_true = true;
            continue;
        }
        if projected.insert(conjunct) {
            let index = source_children
                .iter()
                .position(|&source| source == conjunct)
                .and_then(|index| u32::try_from(index).ok())?;
            projections.push(ProvenanceOrAndProjection { index, conjunct });
        }
    }
    Some(ProvenanceOrAndMapping {
        source,
        target,
        target_children: target_children.to_vec(),
        projections,
        has_true,
    })
}

pub(super) fn conjunctive_transfer_plan_shape_is_valid(
    terms: &mut ay_core::TermStore,
    plan: &ProvenanceOrAndTransferPlan,
) -> bool {
    shape::is_valid(terms, plan)
}

impl Executor {
    pub(super) fn plan_provenance_or_and_transfer(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceOrAndTransferPlan> {
        let [goal] = clause else { return None };
        if !planning.spend_terms(&self.ctx.terms, &[*goal]) {
            return None;
        }
        let (target_disjuncts, target_branches) = target_and_branches(&self.ctx.terms, *goal)?;
        let [source_set] = self
            .proof_problem_assertion_provenance
            .as_ref()?
            .assertion_sources
            .get(goal)?
            .as_slice()
        else {
            return None;
        };
        if !source_set_is_exactly_authored(source_set, source_index) {
            return None;
        }
        let source_set = source_set.clone();
        let mut candidate = None;
        for &source in &source_set {
            let (_, parsed) = source_index.get(originals, source)?;
            let TermData::App(Symbol::Named(head), disjuncts) = self.ctx.terms.get(source) else {
                continue;
            };
            if head != "or" || !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len()) {
                continue;
            }
            let disjuncts = disjuncts.clone();
            if !planning.spend_surface(source, parsed) {
                return None;
            }
            if let Some(branches) =
                authenticate_flat_and_or_surface_prechecked(&mut self.ctx, parsed, &disjuncts)
            {
                if candidate.is_some() {
                    return None;
                }
                candidate = Some((source, disjuncts, branches));
            }
        }
        let (orig, source_disjuncts, branches) = candidate?;
        let supports: Vec<TermId> = source_set
            .iter()
            .copied()
            .filter(|&source| source != orig)
            .collect();
        let support_set: HashSet<TermId> = supports.iter().copied().collect();
        if support_set.len() != supports.len() || !planning.spend_work(supports.len()) {
            return None;
        }
        let (_, parsed_orig) = source_index.get(originals, orig)?;
        if !planning.spend_surface(orig, parsed_orig) {
            return None;
        }
        let FrontendTerm::App(_, surface_disjuncts) = strip_frontend_annotations(parsed_orig)
        else {
            return None;
        };
        let mut outcomes = Vec::with_capacity(branches.len());
        let mut projections = 0usize;
        for (surface_disjunct, branch) in surface_disjuncts.iter().zip(&branches) {
            let source_children = flat_bool_and_children(&self.ctx.terms, branch.disjunct, false)?;
            let FrontendTerm::App(_, surface_conjuncts) =
                strip_frontend_annotations(surface_disjunct)
            else {
                return None;
            };
            let mut refutation = None;
            for (surface, &conjunct) in surface_conjuncts.iter().zip(&branch.conjuncts) {
                if !surface_is_direct_arithmetic_literal_prechecked(&mut self.ctx, surface) {
                    continue;
                }
                let mut rows = Vec::with_capacity(supports.len() + 1);
                rows.push(conjunct);
                rows.extend(supports.iter().copied());
                if !unique_atoms(&self.ctx.terms, &rows) {
                    continue;
                }
                if !planning.spend_farkas_attempt(&self.ctx.terms, &rows) {
                    return None;
                }
                let Some(lemma) = self
                    .plan_provenance_farkas_conflict(conjunct, &supports)
                    .filter(|lemma| {
                        super::direct_refutation_shape(&mut self.ctx.terms, conjunct, lemma)
                            && unique_atoms(&self.ctx.terms, &lemma.clause)
                            && retained_original_rows_are_signable(
                                &mut self.ctx,
                                &lemma.supports,
                                originals,
                                source_index,
                                planning,
                            )
                    })
                else {
                    continue;
                };
                let index = source_children.iter().position(|&term| term == conjunct)?;
                refutation = Some(ProvenanceOrAndRefutation {
                    disjunct: branch.disjunct,
                    conjunct,
                    index: u32::try_from(index).ok()?,
                    lemma,
                });
                break;
            }
            if let Some(refutation) = refutation {
                outcomes.push(ProvenanceOrAndTransferOutcome::Refute(refutation));
                continue;
            }
            let mut selected = None;
            for (target, target_children) in &target_branches {
                if source_disjuncts.contains(target) {
                    continue;
                }
                let scan = source_children
                    .len()
                    .saturating_add(target_children.len())
                    .saturating_mul(source_children.len().saturating_add(1));
                if !planning.spend_work(scan) {
                    return None;
                }
                if let Some(mapping) = mapping_for_target(
                    &mut self.ctx.terms,
                    branch.disjunct,
                    &source_children,
                    *target,
                    target_children,
                    &support_set,
                ) {
                    if selected.is_some() {
                        return None;
                    }
                    selected = Some(mapping);
                }
            }
            let mapping = selected?;
            projections = projections.checked_add(mapping.projections.len())?;
            if projections > MAX_CONJUNCTIVE_TRANSFER_PROJECTIONS {
                return None;
            }
            outcomes.push(ProvenanceOrAndTransferOutcome::Map(mapping));
        }
        let remaining_targets = remaining_target_set(&source_disjuncts, &outcomes)?;
        let plan = ProvenanceOrAndTransferPlan {
            goal: *goal,
            orig,
            source_disjuncts,
            target_disjuncts,
            remaining_targets,
            authored_sources: source_set,
            outcomes,
        };
        conjunctive_transfer_plan_shape_is_valid(&mut self.ctx.terms, &plan).then_some(plan)
    }
}
