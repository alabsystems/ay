// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source-to-target transfer for provenance-authenticated OR leaves.

use ay_core::term::TermData;
use ay_core::TermId;
use ay_frontend::command::Term as FrontendTerm;

use super::proof_trust_surgery_ite::ProvenanceFarkasLemma;
use super::proof_trust_surgery_provenance::{
    branch_resolution_shape_unambiguous, complement_of, retained_original_rows_are_signable,
    surface_arithmetic_ite_matches, unique_atoms, AuthenticatedProvenanceOr, OriginalSourceIndex,
    ProvenanceSurfaceAudit, SurgeryPlanningBudget, MAX_PROVENANCE_REPAIR_TERMS,
};
use super::Executor;

pub(super) struct ProvenanceOrTransferPlan {
    pub(super) goal: TermId,
    pub(super) orig: TermId,
    pub(super) source_disjuncts: Vec<TermId>,
    pub(super) target_disjuncts: Vec<TermId>,
    pub(super) authored_sources: Vec<TermId>,
    pub(super) bridges: Vec<ProvenanceOrBridge>,
}

pub(super) enum ProvenanceOrBridge {
    Farkas {
        source: TermId,
        target: TermId,
        lemma: ProvenanceFarkasLemma,
    },
    Ite(ProvenanceOrIteBridge),
}

impl ProvenanceOrBridge {
    pub(super) fn endpoints(&self) -> (TermId, TermId) {
        match self {
            Self::Farkas { source, target, .. } => (*source, *target),
            Self::Ite(plan) => (plan.source, plan.target),
        }
    }
}

pub(super) struct ProvenanceOrIteBridge {
    pub(super) source: TermId,
    pub(super) target: TermId,
    pub(super) ite_orig: TermId,
    pub(super) cond: TermId,
    pub(super) source_then: TermId,
    pub(super) source_else: TermId,
    pub(super) target_then: TermId,
    pub(super) target_else: TermId,
    pub(super) then_lemma: ProvenanceFarkasLemma,
    pub(super) else_lemma: ProvenanceFarkasLemma,
}

impl ProvenanceOrTransferPlan {
    pub(super) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        audit.protect_rigid_operand(terms, self.goal);
        for bridge in &self.bridges {
            match bridge {
                ProvenanceOrBridge::Farkas {
                    source,
                    target,
                    lemma,
                } => {
                    for operand in [*source, *target] {
                        audit.protect_farkas_operand(terms, operand);
                    }
                    audit.protect_farkas_lemma(terms, &lemma.clause, &lemma.farkas);
                }
                ProvenanceOrBridge::Ite(ite) => {
                    audit.protect_operand(terms, ite.ite_orig);
                    audit.protect_rigid_operand(terms, ite.target);
                    audit.protect_operand(terms, ite.cond);
                    for operand in [
                        ite.source,
                        ite.source_then,
                        ite.source_else,
                        ite.target_then,
                        ite.target_else,
                    ] {
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

fn direct_bridge_shape(
    terms: &mut ay_core::TermStore,
    source: TermId,
    target: TermId,
    lemma: &ProvenanceFarkasLemma,
) -> bool {
    let source_blocker = complement_of(terms, source);
    if !unique_atoms(terms, &lemma.clause)
        || lemma
            .clause
            .iter()
            .filter(|&&literal| literal == source_blocker)
            .count()
            != 1
        || lemma
            .clause
            .iter()
            .filter(|&&literal| literal == target)
            .count()
            != 1
    {
        return false;
    }
    let mut remaining = lemma.clause.clone();
    for &support in &lemma.supports {
        let blocker = complement_of(terms, support);
        let Some(position) = remaining.iter().position(|&literal| literal == blocker) else {
            return false;
        };
        let _ = remaining.remove(position);
    }
    remaining == [source_blocker, target]
}

pub(super) fn ite_transfer_branch_shape(
    terms: &mut ay_core::TermStore,
    target: TermId,
    guard: TermId,
    source_branch: TermId,
    target_branch: TermId,
    source_disjunct: TermId,
    lemma: &ProvenanceFarkasLemma,
) -> bool {
    if lemma
        .supports
        .iter()
        .filter(|&&support| support == source_disjunct)
        .count()
        != 1
        || !branch_resolution_shape_unambiguous(
            terms,
            target,
            guard,
            source_branch,
            target_branch,
            &lemma.clause,
        )
    {
        return false;
    }
    let source_branch_blocker = complement_of(terms, source_branch);
    let source_disjunct_blocker = complement_of(terms, source_disjunct);
    let mut remaining = vec![target, guard];
    remaining.extend(
        lemma
            .clause
            .iter()
            .copied()
            .filter(|&literal| literal != target_branch),
    );
    let Some(position) = remaining
        .iter()
        .position(|&literal| literal == source_branch_blocker)
    else {
        return false;
    };
    let _ = remaining.remove(position);
    for &support in &lemma.supports {
        if support == source_disjunct {
            continue;
        }
        let blocker = complement_of(terms, support);
        let Some(position) = remaining.iter().position(|&literal| literal == blocker) else {
            return false;
        };
        let _ = remaining.remove(position);
    }
    unique_atoms(terms, &remaining) && remaining == [target, guard, source_disjunct_blocker]
}

impl Executor {
    pub(super) fn plan_provenance_or_exact_transfer(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        budget: &mut SurgeryPlanningBudget,
    ) -> Option<ProvenanceOrTransferPlan> {
        let [goal] = clause else { return None };
        let TermData::App(_, target_disjuncts) = self.ctx.terms.get(*goal).clone() else {
            return None;
        };
        if !(2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&target_disjuncts.len())
            || !unique_atoms(&self.ctx.terms, &target_disjuncts)
        {
            return None;
        }
        let authenticated =
            self.authenticate_provenance_or(*goal, originals, source_index, budget)?;
        let AuthenticatedProvenanceOr {
            orig,
            disjuncts: source_disjuncts,
            supports,
            authored_sources,
        } = authenticated;
        if source_disjuncts.len() != target_disjuncts.len() {
            return None;
        }
        let mut all_disjuncts = source_disjuncts.clone();
        all_disjuncts.extend_from_slice(&target_disjuncts);
        if !unique_atoms(&self.ctx.terms, &all_disjuncts) {
            return None;
        }

        let mut candidates: Vec<Vec<Option<ProvenanceOrBridge>>> = source_disjuncts
            .iter()
            .map(|_| (0..target_disjuncts.len()).map(|_| None).collect())
            .collect();
        for (source_position, &source) in source_disjuncts.iter().enumerate() {
            for (target_index, &target) in target_disjuncts.iter().enumerate() {
                candidates[source_position][target_index] = self
                    .plan_provenance_or_bridge(
                        source,
                        target,
                        &supports,
                        originals,
                        source_index,
                        budget,
                    )
                    .ok()?;
            }
        }

        // Fail closed unless every source has exactly one target and every
        // target is selected exactly once. This is stricter than merely
        // finding a perfect matching and prevents authority from depending on
        // an arbitrary traversal order.
        let mut selected_targets = Vec::with_capacity(source_disjuncts.len());
        let mut bridges = Vec::with_capacity(source_disjuncts.len());
        for row in &mut candidates {
            let mut present = row
                .iter()
                .enumerate()
                .filter(|(_, bridge)| bridge.is_some());
            let (target_index, _) = present.next()?;
            if present.next().is_some() {
                return None;
            }
            selected_targets.push(target_index);
            bridges.push(row[target_index].take()?);
        }
        selected_targets.sort_unstable();
        selected_targets.dedup();
        if selected_targets.len() != target_disjuncts.len() {
            return None;
        }
        Some(ProvenanceOrTransferPlan {
            goal: *goal,
            orig,
            source_disjuncts,
            target_disjuncts,
            authored_sources,
            bridges,
        })
    }

    fn plan_provenance_or_bridge(
        &mut self,
        source: TermId,
        target: TermId,
        supports: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        budget: &mut SurgeryPlanningBudget,
    ) -> Result<Option<ProvenanceOrBridge>, ()> {
        let mut direct_rows = vec![source];
        direct_rows.extend(supports.iter().copied());
        direct_rows.push(target);
        if !budget.spend_farkas_attempt(&self.ctx.terms, &direct_rows) {
            return Err(());
        }
        if let Some(lemma) = self
            .plan_provenance_farkas_implication(source, supports, target)
            .filter(|lemma| {
                direct_bridge_shape(&mut self.ctx.terms, source, target, lemma)
                    && retained_original_rows_are_signable(
                        &mut self.ctx,
                        &lemma.supports,
                        originals,
                        source_index,
                        budget,
                    )
            })
        {
            return Ok(Some(ProvenanceOrBridge::Farkas {
                source,
                target,
                lemma,
            }));
        }

        let TermData::Ite(cond, target_then, target_else) = self.ctx.terms.get(target).clone()
        else {
            return Ok(None);
        };
        let mut candidates = Vec::new();
        for &ite_orig in supports {
            let TermData::Ite(source_cond, source_then, source_else) =
                self.ctx.terms.get(ite_orig).clone()
            else {
                continue;
            };
            let (_, parsed) = source_index.get(originals, ite_orig).ok_or(())?;
            if !budget.spend_surface(ite_orig, parsed) {
                return Err(());
            }
            if source_cond != cond
                || !surface_arithmetic_ite_matches(
                    &mut self.ctx,
                    parsed,
                    &[source_cond, source_then, source_else],
                )
            {
                continue;
            }
            let branch_supports: Vec<TermId> = std::iter::once(source)
                .chain(
                    supports
                        .iter()
                        .copied()
                        .filter(|&support| support != ite_orig),
                )
                .collect();
            let mut then_rows = vec![source_then];
            then_rows.extend(branch_supports.iter().copied());
            then_rows.push(target_then);
            if !budget.spend_farkas_attempt(&self.ctx.terms, &then_rows) {
                return Err(());
            }
            let Some(then_lemma) =
                self.plan_provenance_farkas_implication(source_then, &branch_supports, target_then)
            else {
                continue;
            };
            let not_cond = self.ctx.terms.mk_not_raw(cond);
            if !retained_original_rows_are_signable(
                &mut self.ctx,
                &then_lemma.supports,
                originals,
                source_index,
                budget,
            ) || !ite_transfer_branch_shape(
                &mut self.ctx.terms,
                target,
                not_cond,
                source_then,
                target_then,
                source,
                &then_lemma,
            ) {
                continue;
            }
            let mut else_rows = vec![source_else];
            else_rows.extend(branch_supports.iter().copied());
            else_rows.push(target_else);
            if !budget.spend_farkas_attempt(&self.ctx.terms, &else_rows) {
                return Err(());
            }
            let Some(else_lemma) =
                self.plan_provenance_farkas_implication(source_else, &branch_supports, target_else)
            else {
                continue;
            };
            if !retained_original_rows_are_signable(
                &mut self.ctx,
                &else_lemma.supports,
                originals,
                source_index,
                budget,
            ) || !ite_transfer_branch_shape(
                &mut self.ctx.terms,
                target,
                cond,
                source_else,
                target_else,
                source,
                &else_lemma,
            ) {
                continue;
            }
            candidates.push(ProvenanceOrIteBridge {
                source,
                target,
                ite_orig,
                cond,
                source_then,
                source_else,
                target_then,
                target_else,
                then_lemma,
                else_lemma,
            });
        }
        let mut candidates = candidates.into_iter();
        let candidate = candidates.next();
        if candidates.next().is_some() {
            return Ok(None);
        }
        Ok(candidate.map(ProvenanceOrBridge::Ite))
    }
}
