// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-role registration for conjunctive provenance-OR transfer.

use super::{ProvenanceOrAndTransferOutcome, ProvenanceOrAndTransferPlan};
use crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProvenanceSurfaceAudit;

pub(super) fn protect_surface_operands(
    plan: &ProvenanceOrAndTransferPlan,
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut ay_core::TermStore,
) {
    let _ =
        audit.protect_or_decomposition_permutation_role(terms, plan.orig, &plan.source_disjuncts);
    audit.protect_rigid_root(terms, plan.goal);
    let mut needs_true = false;
    for outcome in &plan.outcomes {
        match outcome {
            ProvenanceOrAndTransferOutcome::Refute(refutation) => {
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
            ProvenanceOrAndTransferOutcome::Map(mapping) => {
                needs_true |= mapping.has_true;
                for projection in &mapping.projections {
                    let _ = audit.protect_and_projection_role(
                        terms,
                        mapping.source,
                        projection.index,
                        projection.conjunct,
                    );
                }
                let _ = audit.protect_and_introduction_role(terms, mapping.target);
            }
        }
    }
    if !plan.remaining_targets.is_empty() {
        let _ = audit.protect_or_projection_roles(
            terms,
            plan.goal,
            &plan.target_disjuncts,
            plan.remaining_targets.len(),
        );
    }
    if needs_true {
        let truth = terms.mk_bool(true);
        audit.protect_rigid_root(terms, truth);
    }
}
