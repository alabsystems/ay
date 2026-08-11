// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact refutation of authored flat-AND branches of a provenance OR.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;

use super::super::proof_surface_syntax::{parsed_term_is_binder_free, strip_frontend_annotations};
#[cfg(test)]
use super::super::proof_trust_surgery_provenance::surface_source_is_bounded;
use super::super::proof_trust_surgery_provenance::{
    complement_of, retained_original_rows_are_signable, source_set_is_exactly_authored,
    surface_is_direct_arithmetic_literal_prechecked, unique_atoms, OriginalSourceIndex,
    SurgeryPlanningBudget, MAX_PROVENANCE_REPAIR_TERMS,
};
use super::super::Executor;
use super::{direct_refutation_shape, ProvenanceOrAndConflictPlan, ProvenanceOrAndRefutation};

pub(super) const MAX_CONJUNCTIVE_SOURCE_TERMS: usize =
    MAX_PROVENANCE_REPAIR_TERMS * MAX_PROVENANCE_REPAIR_TERMS;

pub(super) struct AuthenticatedFlatAndBranch {
    pub(super) disjunct: TermId,
    /// Canonical conjunct ids in exact authored surface order.
    pub(super) conjuncts: Vec<TermId>,
}

pub(super) fn exact_term_permutation(actual: &[TermId], expected: &[TermId]) -> bool {
    if actual.len() != expected.len() {
        return false;
    }
    let mut actual = actual.to_vec();
    let mut expected = expected.to_vec();
    actual.sort_unstable();
    expected.sort_unstable();
    actual == expected
}

pub(super) fn authenticate_flat_and_or_surface_prechecked(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    disjuncts: &[TermId],
) -> Option<Vec<AuthenticatedFlatAndBranch>> {
    let FrontendTerm::App(head, surface_disjuncts) = strip_frontend_annotations(parsed) else {
        return None;
    };
    if head != "or"
        || !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
        || surface_disjuncts.len() != disjuncts.len()
        || !parsed_term_is_binder_free(parsed)
    {
        return None;
    }
    let mut total_conjuncts = 0usize;
    let mut surface_disjunct_ids = Vec::with_capacity(surface_disjuncts.len());
    let mut branches = Vec::with_capacity(surface_disjuncts.len());
    for surface in surface_disjuncts {
        let disjunct = ctx.elaborate_surface_subterm(surface)?;
        surface_disjunct_ids.push(disjunct);
        let conjuncts = match ctx.terms.get(disjunct) {
            TermData::App(Symbol::Named(head), conjuncts)
                if head == "and"
                    && *ctx.terms.sort(disjunct) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&conjuncts.len())
                    && conjuncts
                        .iter()
                        .all(|&term| *ctx.terms.sort(term) == Sort::Bool) =>
            {
                conjuncts.clone()
            }
            _ => return None,
        };
        let FrontendTerm::App(head, surface_conjuncts) = strip_frontend_annotations(surface) else {
            return None;
        };
        if head != "and"
            || surface_conjuncts.len() != conjuncts.len()
            || surface_conjuncts.iter().any(|term| {
                matches!(
                    strip_frontend_annotations(term),
                    FrontendTerm::App(child_head, _) if child_head == "and"
                )
            })
            || !unique_atoms(&ctx.terms, &conjuncts)
        {
            return None;
        }
        let surface_conjunct_ids = surface_conjuncts
            .iter()
            .map(|surface| ctx.elaborate_surface_subterm(surface))
            .collect::<Option<Vec<_>>>()?;
        if !exact_term_permutation(&surface_conjunct_ids, &conjuncts) {
            return None;
        }
        let next = total_conjuncts.checked_add(conjuncts.len())?;
        if next > MAX_CONJUNCTIVE_SOURCE_TERMS {
            return None;
        }
        total_conjuncts = next;
        branches.push(AuthenticatedFlatAndBranch {
            disjunct,
            conjuncts: surface_conjunct_ids,
        });
    }
    (unique_atoms(&ctx.terms, disjuncts)
        && exact_term_permutation(&surface_disjunct_ids, disjuncts))
    .then_some(branches)
}

#[cfg(test)]
pub(super) fn exact_flat_and_or_surface_matches(
    ctx: &mut ay_frontend::Context,
    parsed: &FrontendTerm,
    disjuncts: &[TermId],
) -> bool {
    surface_source_is_bounded(parsed)
        && authenticate_flat_and_or_surface_prechecked(ctx, parsed, disjuncts).is_some()
}

pub(super) fn conjunctive_refutation_shape_is_valid(
    terms: &mut ay_core::TermStore,
    orig: TermId,
    authored_sources: &[TermId],
    refutation: &ProvenanceOrAndRefutation,
) -> bool {
    let disjunct = refutation.disjunct;
    if refutation.lemma.clause.len() > MAX_PROVENANCE_REPAIR_TERMS
        || refutation.lemma.supports.len() >= MAX_PROVENANCE_REPAIR_TERMS
        || refutation.lemma.farkas.coefficients.len() != refutation.lemma.clause.len()
        || !matches!(
            terms.get(disjunct),
            TermData::App(Symbol::Named(head), conjuncts)
                if head == "and"
                    && *terms.sort(disjunct) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&conjuncts.len())
                    && conjuncts.iter().all(|&term| *terms.sort(term) == Sort::Bool)
                    && conjuncts.get(refutation.index as usize)
                        == Some(&refutation.conjunct)
        )
        || !unique_atoms(terms, &[disjunct, refutation.conjunct])
        || {
            let mut rows = Vec::with_capacity(refutation.lemma.supports.len() + 1);
            rows.push(refutation.conjunct);
            rows.extend(refutation.lemma.supports.iter().copied());
            !unique_atoms(terms, &rows)
        }
        || !direct_refutation_shape(terms, refutation.conjunct, &refutation.lemma)
        || refutation
            .lemma
            .supports
            .iter()
            .any(|support| *support == orig || !authored_sources.contains(support))
    {
        return false;
    }
    let mut remaining = refutation.lemma.clause.clone();
    for &support in &refutation.lemma.supports {
        let blocker = complement_of(terms, support);
        let Some(position) = remaining.iter().position(|&literal| literal == blocker) else {
            return false;
        };
        let _ = remaining.remove(position);
    }
    remaining == [complement_of(terms, refutation.conjunct)]
}

fn conjunctive_plan_shape_is_valid(
    terms: &mut ay_core::TermStore,
    plan: &ProvenanceOrAndConflictPlan,
) -> bool {
    if !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&plan.disjuncts.len())
        || plan.refutations.len() != plan.disjuncts.len()
        || plan.authored_sources.len() > MAX_PROVENANCE_REPAIR_TERMS
        || plan.orig == plan.goal
        || !plan.authored_sources.contains(&plan.orig)
        || !unique_atoms(terms, &plan.disjuncts)
        || !exact_term_permutation(
            &plan
                .refutations
                .iter()
                .map(|refutation| refutation.disjunct)
                .collect::<Vec<_>>(),
            &plan.disjuncts,
        )
        || {
            let mut sources = plan.authored_sources.clone();
            sources.sort_unstable();
            sources.dedup();
            sources.len() != plan.authored_sources.len()
        }
        || !matches!(
            terms.get(plan.goal),
            TermData::App(Symbol::Named(head), disjuncts)
                if head == "or"
                    && *terms.sort(plan.goal) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
        )
        || !matches!(
            terms.get(plan.orig),
            TermData::App(Symbol::Named(head), disjuncts)
                if head == "or"
                    && *terms.sort(plan.orig) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
                    && disjuncts.as_slice() == plan.disjuncts.as_slice()
        )
    {
        return false;
    }
    plan.refutations.iter().all(|refutation| {
        conjunctive_refutation_shape_is_valid(terms, plan.orig, &plan.authored_sources, refutation)
    })
}

impl Executor {
    pub(super) fn plan_provenance_or_and_conflict(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceOrAndConflictPlan> {
        let [goal] = clause else { return None };
        if !matches!(
            self.ctx.terms.get(*goal),
            TermData::App(Symbol::Named(head), disjuncts)
                if head == "or"
                    && *self.ctx.terms.sort(*goal) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
        ) {
            return None;
        }
        let source_sets = self
            .proof_problem_assertion_provenance
            .as_ref()?
            .assertion_sources
            .get(goal)?;
        let [source_set] = source_sets.as_slice() else {
            return None;
        };
        if !source_set_is_exactly_authored(source_set, source_index) {
            return None;
        }
        let source_set = source_set.clone();

        let mut candidate = None;
        for &source in &source_set {
            let (_, parsed) = source_index.get(originals, source)?;
            let disjuncts = match self.ctx.terms.get(source) {
                TermData::App(Symbol::Named(head), disjuncts)
                    if head == "or"
                        && *self.ctx.terms.sort(source) == Sort::Bool
                        && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len()) =>
                {
                    disjuncts.clone()
                }
                _ => continue,
            };
            // `surface_source_work` accounts for every subtree with depth and
            // formatting headroom, so one debit covers this complete ordered
            // shape/binder/elaboration pass.
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
        let (orig, disjuncts, branches) = candidate?;
        let supports: Vec<TermId> = source_set
            .iter()
            .copied()
            .filter(|&source| source != orig)
            .collect();
        let (_, parsed_orig) = source_index.get(originals, orig)?;
        // A second complete-source debit covers every direct-literal
        // classification below. The source-work estimate already includes
        // all subtrees rather than charging only the root spelling.
        if !planning.spend_surface(orig, parsed_orig) {
            return None;
        }
        let FrontendTerm::App(_, surface_disjuncts) = strip_frontend_annotations(parsed_orig)
        else {
            return None;
        };

        let mut refutations = Vec::with_capacity(disjuncts.len());
        for (surface_disjunct, branch) in surface_disjuncts.iter().zip(&branches) {
            let disjunct = branch.disjunct;
            let FrontendTerm::App(_, surface_conjuncts) =
                strip_frontend_annotations(surface_disjunct)
            else {
                return None;
            };
            let conjuncts = match self.ctx.terms.get(disjunct) {
                TermData::App(_, conjuncts) => conjuncts.clone(),
                _ => return None,
            };
            let mut selected = None;
            for (surface, &conjunct) in surface_conjuncts.iter().zip(&branch.conjuncts) {
                if !surface_is_direct_arithmetic_literal_prechecked(&mut self.ctx, surface) {
                    continue;
                }
                let mut unique_rows = Vec::with_capacity(supports.len() + 1);
                unique_rows.push(conjunct);
                unique_rows.extend(supports.iter().copied());
                if !unique_atoms(&self.ctx.terms, &unique_rows) {
                    continue;
                }
                if !planning.spend_farkas_attempt(&self.ctx.terms, &unique_rows) {
                    return None;
                }
                let Some(lemma) = self
                    .plan_provenance_farkas_conflict(conjunct, &supports)
                    .filter(|lemma| {
                        direct_refutation_shape(&mut self.ctx.terms, conjunct, lemma)
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
                let index = conjuncts.iter().position(|&term| term == conjunct)?;
                let index = u32::try_from(index).ok()?;
                selected = Some(ProvenanceOrAndRefutation {
                    disjunct,
                    conjunct,
                    index,
                    lemma,
                });
                break;
            }
            refutations.push(selected?);
        }
        let plan = ProvenanceOrAndConflictPlan {
            goal: *goal,
            orig,
            disjuncts,
            authored_sources: source_set,
            refutations,
        };
        conjunctive_plan_shape_is_valid(&mut self.ctx.terms, &plan).then_some(plan)
    }

    pub(in crate::executor::proof_repair) fn emit_provenance_or_and_conflict(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrAndConflictPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        if !conjunctive_plan_shape_is_valid(&mut self.ctx.terms, plan) {
            return None;
        }
        let &or_assume = authored_assumes.get(&plan.orig)?;
        for refutation in &plan.refutations {
            if refutation
                .lemma
                .supports
                .iter()
                .any(|support| !authored_assumes.contains_key(support))
            {
                return None;
            }
        }

        let mut current = proof.add_rule_step(
            AletheRule::Or,
            plan.disjuncts.clone(),
            vec![or_assume],
            Vec::new(),
        );
        let mut or_remaining = plan.disjuncts.clone();
        for refutation in &plan.refutations {
            let mut branch = proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: refutation.lemma.clause.clone(),
                farkas: Some(refutation.lemma.farkas.clone()),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let mut lemma_remaining = refutation.lemma.clause.clone();
            for &support in &refutation.lemma.supports {
                let blocker = complement_of(&mut self.ctx.terms, support);
                let index = lemma_remaining
                    .iter()
                    .position(|&literal| literal == blocker)?;
                let _ = lemma_remaining.remove(index);
                branch = proof.add_resolution(
                    lemma_remaining.clone(),
                    support,
                    branch,
                    authored_assumes[&support],
                );
            }
            let not_conjunct = complement_of(&mut self.ctx.terms, refutation.conjunct);
            if lemma_remaining != [not_conjunct] {
                return None;
            }
            let not_disjunct = complement_of(&mut self.ctx.terms, refutation.disjunct);
            let projection = proof.add_rule_step(
                AletheRule::AndPos(refutation.index),
                vec![not_disjunct, refutation.conjunct],
                Vec::new(),
                vec![refutation.disjunct],
            );
            let negated_disjunct =
                proof.add_resolution(vec![not_disjunct], refutation.conjunct, branch, projection);
            let index = or_remaining
                .iter()
                .position(|&literal| literal == refutation.disjunct)?;
            let _ = or_remaining.remove(index);
            current = proof.add_resolution(
                or_remaining.clone(),
                refutation.disjunct,
                current,
                negated_disjunct,
            );
        }
        if !or_remaining.is_empty() {
            return None;
        }
        Some(proof.add_rule_step(
            AletheRule::Weakening,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }
}
