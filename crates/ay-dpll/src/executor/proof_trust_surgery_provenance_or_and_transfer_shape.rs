// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transactional shape revalidation for conjunctive provenance-OR transfer.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, Symbol, TermId};

use super::super::and_conflict::{conjunctive_refutation_shape_is_valid, exact_term_permutation};
use super::{
    flat_bool_and_children, mapping_for_target, remaining_target_set, target_and_branches,
    ProvenanceOrAndTransferOutcome, ProvenanceOrAndTransferPlan,
    MAX_CONJUNCTIVE_TRANSFER_PROJECTIONS,
};
use crate::executor::proof_repair::proof_trust_surgery_provenance::{
    unique_atoms, MAX_PROVENANCE_REPAIR_TERMS,
};

pub(super) fn is_valid(terms: &mut ay_core::TermStore, plan: &ProvenanceOrAndTransferPlan) -> bool {
    let Some((target_disjuncts, target_branches)) = target_and_branches(terms, plan.goal) else {
        return false;
    };
    if target_disjuncts != plan.target_disjuncts
        || remaining_target_set(&plan.source_disjuncts, &plan.outcomes).as_deref()
            != Some(plan.remaining_targets.as_slice())
        || plan
            .remaining_targets
            .iter()
            .any(|target| !plan.target_disjuncts.contains(target))
        || plan.orig == plan.goal
        || plan.remaining_targets.is_empty()
        || !plan.authored_sources.contains(&plan.orig)
        || plan.authored_sources.len() > MAX_PROVENANCE_REPAIR_TERMS
        || plan.outcomes.len() != plan.source_disjuncts.len()
        || !unique_atoms(terms, &plan.source_disjuncts)
        || !exact_term_permutation(
            &plan
                .outcomes
                .iter()
                .map(ProvenanceOrAndTransferOutcome::source)
                .collect::<Vec<_>>(),
            &plan.source_disjuncts,
        )
        || {
            let mut sources = plan.authored_sources.clone();
            sources.sort_unstable();
            sources.dedup();
            sources.len() != plan.authored_sources.len()
        }
        || !matches!(
            terms.get(plan.orig),
            TermData::App(Symbol::Named(head), disjuncts)
                if head == "or"
                    && *terms.sort(plan.orig) == Sort::Bool
                    && (2..=MAX_PROVENANCE_REPAIR_TERMS).contains(&disjuncts.len())
                    && disjuncts.as_slice() == plan.source_disjuncts.as_slice()
                    && disjuncts
                        .iter()
                        .all(|&disjunct| *terms.sort(disjunct) == Sort::Bool)
        )
    {
        return false;
    }
    let supports: HashSet<TermId> = plan
        .authored_sources
        .iter()
        .copied()
        .filter(|&source| source != plan.orig)
        .collect();
    let mut mapped = 0usize;
    let mut projection_count = 0usize;
    for outcome in &plan.outcomes {
        if flat_bool_and_children(terms, outcome.source(), false).is_none() {
            return false;
        }
        match outcome {
            ProvenanceOrAndTransferOutcome::Refute(refutation) => {
                if !conjunctive_refutation_shape_is_valid(
                    terms,
                    plan.orig,
                    &plan.authored_sources,
                    refutation,
                ) {
                    return false;
                }
            }
            ProvenanceOrAndTransferOutcome::Map(mapping) => {
                if plan.source_disjuncts.contains(&mapping.target) {
                    return false;
                }
                let Some(source_children) = flat_bool_and_children(terms, mapping.source, false)
                else {
                    return false;
                };
                let Some((_, target_children)) = target_branches
                    .iter()
                    .find(|(target, _)| *target == mapping.target)
                else {
                    return false;
                };
                let Some(expected) = mapping_for_target(
                    terms,
                    mapping.source,
                    &source_children,
                    mapping.target,
                    target_children,
                    &supports,
                ) else {
                    return false;
                };
                if expected.has_true != mapping.has_true
                    || expected.target_children != mapping.target_children
                    || expected.projections.len() != mapping.projections.len()
                    || expected.projections.iter().zip(&mapping.projections).any(
                        |(expected, actual)| {
                            expected.index != actual.index || expected.conjunct != actual.conjunct
                        },
                    )
                {
                    return false;
                }
                mapped += 1;
                projection_count = match projection_count.checked_add(mapping.projections.len()) {
                    Some(count) => count,
                    None => return false,
                };
            }
        }
    }
    mapped > 0
        && !plan.remaining_targets.is_empty()
        && projection_count <= MAX_CONJUNCTIVE_TRANSFER_PROJECTIONS
}
