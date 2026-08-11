// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provenance-authenticated repair of preprocessed disjunction leaves.

use ay_core::term::TermData;
use ay_core::{Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::proof_surface_syntax::strip_frontend_annotations;
use super::proof_trust_surgery_ite::ProvenanceFarkasLemma;
use super::proof_trust_surgery_provenance::{
    complement_of, retained_original_rows_are_signable, surface_arithmetic_ite_matches,
    unique_atoms, AuthenticatedProvenanceOr, OriginalSourceIndex, ProvenanceSurfaceAudit,
    SurgeryPlanningBudget, MAX_PROVENANCE_REPAIR_TERMS,
};
use super::proof_trust_surgery_provenance_or_transfer::ProvenanceOrTransferPlan;
use super::Executor;

#[path = "proof_trust_surgery_provenance_or_and.rs"]
mod and_conflict;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_carcara_tests.rs"]
mod and_conflict_carcara_tests;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_fixture.rs"]
mod and_conflict_fixture;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_tests.rs"]
mod and_conflict_tests;
#[cfg(test)]
#[path = "proof_trust_surgery_provenance_or_and_surface_tests.rs"]
mod and_surface_tests;
#[path = "proof_trust_surgery_provenance_or_and_transfer.rs"]
mod and_transfer;
pub(in crate::executor::proof_repair) use and_transfer::ProvenanceOrAndTransferPlan;

pub(super) enum ProvenanceOrPlan {
    Conflict(ProvenanceOrConflictPlan),
    ConjunctiveConflict(ProvenanceOrAndConflictPlan),
    ConjunctiveTransfer(ProvenanceOrAndTransferPlan),
    ExactTransfer(ProvenanceOrTransferPlan),
}

impl ProvenanceOrPlan {
    pub(super) fn authored_sources(&self) -> &[TermId] {
        match self {
            Self::Conflict(plan) => &plan.authored_sources,
            Self::ConjunctiveConflict(plan) => &plan.authored_sources,
            Self::ConjunctiveTransfer(plan) => &plan.authored_sources,
            Self::ExactTransfer(plan) => &plan.authored_sources,
        }
    }

    pub(super) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        let orig = match self {
            Self::ExactTransfer(plan) => plan.orig,
            Self::Conflict(plan) => plan.orig,
            Self::ConjunctiveConflict(plan) => plan.orig,
            Self::ConjunctiveTransfer(plan) => plan.orig,
        };
        // `or` decomposes this exact authored premise; its whole spelling is
        // therefore a rule operand, not merely provenance metadata.
        audit.protect_operand(terms, orig);
        match self {
            Self::ExactTransfer(plan) => plan.protect_surface_operands(audit, terms),
            Self::ConjunctiveConflict(plan) => {
                // This goal is introduced only by weakening an independently
                // derived empty clause. Its root must not be re-spelled, but
                // authenticated descendant spellings do not participate in a
                // positional inference here; copied downstream roles audit
                // any such descendants independently.
                audit.protect_rigid_root(terms, plan.goal);
                let _ = audit.protect_or_decomposition_permutation_role(
                    terms,
                    plan.orig,
                    &plan.disjuncts,
                );
                for refutation in &plan.refutations {
                    let _ = audit.protect_and_projection_role(
                        terms,
                        refutation.disjunct,
                        refutation.index,
                        refutation.conjunct,
                    );
                    audit.protect_farkas_operand(terms, refutation.conjunct);
                    audit.protect_farkas_lemma(
                        terms,
                        &refutation.lemma.clause,
                        &refutation.lemma.farkas,
                    );
                }
            }
            Self::ConjunctiveTransfer(plan) => {
                plan.protect_surface_operands(audit, terms);
            }
            Self::Conflict(plan) => {
                audit.protect_rigid_operand(terms, plan.goal);
                for refutation in &plan.refutations {
                    match refutation {
                        ProvenanceOrRefutation::Farkas { disjunct, lemma } => {
                            audit.protect_farkas_operand(terms, *disjunct);
                            audit.protect_farkas_lemma(terms, &lemma.clause, &lemma.farkas);
                        }
                        ProvenanceOrRefutation::Ite(ite) => {
                            audit.protect_operand(terms, ite.ite_orig);
                            audit.protect_operand(terms, ite.cond);
                            for operand in [ite.disjunct, ite.source_then, ite.source_else] {
                                audit.protect_farkas_operand(terms, operand);
                            }
                            audit.protect_farkas_lemma(
                                terms,
                                &ite.then_lemma.clause,
                                &ite.then_lemma.farkas,
                            );
                            audit.protect_farkas_lemma(
                                terms,
                                &ite.else_lemma.clause,
                                &ite.else_lemma.farkas,
                            );
                        }
                    }
                }
            }
        }
    }
}

pub(super) struct ProvenanceOrConflictPlan {
    pub(super) goal: TermId,
    pub(super) orig: TermId,
    pub(super) disjuncts: Vec<TermId>,
    pub(super) authored_sources: Vec<TermId>,
    pub(super) refutations: Vec<ProvenanceOrRefutation>,
}

pub(super) struct ProvenanceOrAndConflictPlan {
    pub(super) goal: TermId,
    pub(super) orig: TermId,
    pub(super) disjuncts: Vec<TermId>,
    pub(super) authored_sources: Vec<TermId>,
    pub(super) refutations: Vec<ProvenanceOrAndRefutation>,
}

pub(super) struct ProvenanceOrAndRefutation {
    pub(super) disjunct: TermId,
    pub(super) conjunct: TermId,
    pub(super) index: u32,
    pub(super) lemma: ProvenanceFarkasLemma,
}

pub(super) enum ProvenanceOrRefutation {
    Farkas {
        disjunct: TermId,
        lemma: ProvenanceFarkasLemma,
    },
    Ite(ProvenanceOrIteRefutation),
}

pub(super) struct ProvenanceOrIteRefutation {
    pub(super) disjunct: TermId,
    pub(super) ite_orig: TermId,
    pub(super) cond: TermId,
    pub(super) source_then: TermId,
    pub(super) source_else: TermId,
    pub(super) then_lemma: ProvenanceFarkasLemma,
    pub(super) else_lemma: ProvenanceFarkasLemma,
}

/// Surface-preserving plans and raw normalization bridges require opposite
/// global override policies. A proof containing both must fail closed.
pub(super) fn surface_override_policy_allows(
    keeps_surface_overrides: bool,
    has_normalization_bridges: bool,
) -> bool {
    !(keeps_surface_overrides && has_normalization_bridges)
}

fn direct_refutation_shape(
    terms: &mut ay_core::TermStore,
    disjunct: TermId,
    lemma: &ProvenanceFarkasLemma,
) -> bool {
    let blocker = complement_of(terms, disjunct);
    if lemma
        .clause
        .iter()
        .filter(|&&literal| literal == blocker)
        .count()
        != 1
        || !unique_atoms(terms, &lemma.clause)
    {
        return false;
    }
    let mut remaining = lemma.clause.clone();
    for &support in &lemma.supports {
        let support_blocker = complement_of(terms, support);
        let Some(index) = remaining
            .iter()
            .position(|&literal| literal == support_blocker)
        else {
            return false;
        };
        let _ = remaining.remove(index);
    }
    remaining == [blocker]
}

pub(super) fn ite_refutation_branch_shape(
    terms: &mut ay_core::TermStore,
    guard: TermId,
    source_branch: TermId,
    disjunct: TermId,
    lemma: &ProvenanceFarkasLemma,
) -> bool {
    let source_blocker = complement_of(terms, source_branch);
    let disjunct_blocker = complement_of(terms, disjunct);
    if !lemma.supports.contains(&disjunct)
        || lemma
            .clause
            .iter()
            .filter(|&&literal| literal == source_blocker)
            .count()
            != 1
        || !unique_atoms(terms, &[guard, source_branch])
        || !unique_atoms(terms, &lemma.clause)
    {
        return false;
    }
    let mut remaining = vec![guard];
    remaining.extend(
        lemma
            .clause
            .iter()
            .copied()
            .filter(|&literal| literal != source_blocker),
    );
    if !unique_atoms(terms, &remaining) {
        return false;
    }
    for &support in &lemma.supports {
        if support == disjunct {
            continue;
        }
        let support_blocker = complement_of(terms, support);
        let Some(index) = remaining
            .iter()
            .position(|&literal| literal == support_blocker)
        else {
            return false;
        };
        let _ = remaining.remove(index);
    }
    unique_atoms(terms, &remaining) && remaining == [guard, disjunct_blocker]
}

impl Executor {
    /// Recover a singleton trust clause that is exactly one authored OR.
    ///
    /// This intentionally does not reason from structural similarity. The
    /// preprocessor must record one unique bounded source set containing the
    /// target, and that canonical target must have one unambiguous parsed
    /// top-level `or` assertion. Other recorded sources are harmless because
    /// the target independently has authored authority. The repair can then
    /// replace the trust leaf with an ordinary Assume of that exact premise,
    /// regardless of nested Boolean/ITE structure inside its disjuncts.
    pub(super) fn plan_exact_provenance_or_assume(
        &self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<TermId> {
        let [goal] = clause else {
            return None;
        };
        if !matches!(
            self.ctx.terms.get(*goal),
            TermData::App(Symbol::Named(op), disjuncts) if op == "or" && disjuncts.len() >= 2
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
        if source_set.is_empty()
            || source_set.len() > MAX_PROVENANCE_REPAIR_TERMS
            || !source_set.contains(goal)
        {
            return None;
        }
        let (_, parsed) = source_index.get(originals, *goal)?;
        if !planning.spend_surface(*goal, parsed) {
            return None;
        }
        if !matches!(
            strip_frontend_annotations(parsed),
            FrontendTerm::App(op, disjuncts) if op == "or" && disjuncts.len() >= 2
        ) {
            return None;
        }
        Some(*goal)
    }

    pub(super) fn plan_provenance_or(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        budget: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceOrPlan> {
        if let Some(plan) =
            self.plan_provenance_or_exact_transfer(clause, originals, source_index, budget)
        {
            return Some(ProvenanceOrPlan::ExactTransfer(plan));
        }
        self.plan_provenance_or_conflict(clause, originals, source_index, budget)
            .map(ProvenanceOrPlan::Conflict)
            .or_else(|| {
                self.plan_provenance_or_and_conflict(clause, originals, source_index, budget)
                    .map(ProvenanceOrPlan::ConjunctiveConflict)
            })
            .or_else(|| {
                self.plan_provenance_or_and_transfer(clause, originals, source_index, budget)
                    .map(ProvenanceOrPlan::ConjunctiveTransfer)
            })
    }

    /// Prove the unique exact provenance source set inconsistent by splitting
    /// its authored OR. The derived empty clause can soundly be weakened to
    /// the preprocessed target OR, avoiding any heuristic source/target leaf
    /// pairing when inconsistent arithmetic branches imply every target.
    pub(super) fn plan_provenance_or_conflict(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceOrConflictPlan> {
        let [goal] = clause else { return None };
        let authenticated =
            self.authenticate_provenance_or(*goal, originals, source_index, planning)?;
        let AuthenticatedProvenanceOr {
            orig,
            disjuncts,
            supports,
            authored_sources,
        } = authenticated;

        let mut refutations = Vec::with_capacity(disjuncts.len());
        for &disjunct in &disjuncts {
            let mut rows = vec![disjunct];
            rows.extend(supports.iter().copied());
            if !planning.spend_farkas_attempt(&self.ctx.terms, &rows) {
                return None;
            }
            if let Some(lemma) = self
                .plan_provenance_farkas_conflict(disjunct, &supports)
                .filter(|lemma| {
                    direct_refutation_shape(&mut self.ctx.terms, disjunct, lemma)
                        && retained_original_rows_are_signable(
                            &mut self.ctx,
                            &lemma.supports,
                            originals,
                            source_index,
                            planning,
                        )
                })
            {
                refutations.push(ProvenanceOrRefutation::Farkas { disjunct, lemma });
                continue;
            }

            let mut ite_candidates = Vec::new();
            for &ite_orig in &supports {
                let (_, parsed) = source_index.get(originals, ite_orig)?;
                if !planning.spend_surface(ite_orig, parsed) {
                    return None;
                }
                let TermData::Ite(cond, source_then, source_else) =
                    self.ctx.terms.get(ite_orig).clone()
                else {
                    continue;
                };
                if !surface_arithmetic_ite_matches(
                    &mut self.ctx,
                    parsed,
                    &[cond, source_then, source_else],
                ) {
                    continue;
                }
                let branch_supports: Vec<TermId> = std::iter::once(disjunct)
                    .chain(
                        supports
                            .iter()
                            .copied()
                            .filter(|&source| source != ite_orig),
                    )
                    .collect();
                let mut then_rows = vec![source_then];
                then_rows.extend(branch_supports.iter().copied());
                if !planning.spend_farkas_attempt(&self.ctx.terms, &then_rows) {
                    return None;
                }
                let Some(then_lemma) =
                    self.plan_provenance_farkas_conflict(source_then, &branch_supports)
                else {
                    continue;
                };
                let mut else_rows = vec![source_else];
                else_rows.extend(branch_supports.iter().copied());
                if !planning.spend_farkas_attempt(&self.ctx.terms, &else_rows) {
                    return None;
                }
                let Some(else_lemma) =
                    self.plan_provenance_farkas_conflict(source_else, &branch_supports)
                else {
                    continue;
                };
                if !retained_original_rows_are_signable(
                    &mut self.ctx,
                    &then_lemma.supports,
                    originals,
                    source_index,
                    planning,
                ) || !retained_original_rows_are_signable(
                    &mut self.ctx,
                    &else_lemma.supports,
                    originals,
                    source_index,
                    planning,
                ) {
                    continue;
                }
                let not_cond = self.ctx.terms.mk_not_raw(cond);
                if !ite_refutation_branch_shape(
                    &mut self.ctx.terms,
                    not_cond,
                    source_then,
                    disjunct,
                    &then_lemma,
                ) || !ite_refutation_branch_shape(
                    &mut self.ctx.terms,
                    cond,
                    source_else,
                    disjunct,
                    &else_lemma,
                ) {
                    continue;
                }
                ite_candidates.push(ProvenanceOrIteRefutation {
                    disjunct,
                    ite_orig,
                    cond,
                    source_then,
                    source_else,
                    then_lemma,
                    else_lemma,
                });
            }
            let mut ite_candidates = ite_candidates.into_iter();
            let candidate = ite_candidates.next()?;
            if ite_candidates.next().is_some() {
                return None;
            }
            refutations.push(ProvenanceOrRefutation::Ite(candidate));
        }

        Some(ProvenanceOrConflictPlan {
            goal: *goal,
            orig,
            disjuncts,
            authored_sources,
            refutations,
        })
    }
}
