// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact validation and lifecycle sanitation for proof Farkas annotations.

use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, TermId, TermStore};

pub(super) fn blocking_clause_to_conflict(
    terms: &TermStore,
    clause: &[TermId],
) -> Vec<ay_core::TheoryLit> {
    clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => ay_core::TheoryLit::new(*inner, true),
            _ => ay_core::TheoryLit::new(literal, false),
        })
        .collect()
}

pub(in crate::executor) fn certificate_valid_for_blocking_clause(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &ay_core::FarkasAnnotation,
) -> bool {
    ay_core::proof_validation::verify_farkas_conflict_lits_full(
        terms,
        &blocking_clause_to_conflict(terms, clause),
        farkas,
    )
    .is_ok()
}

/// Clear arithmetic proof annotations that no longer certify their exact
/// clause after surface-syntax rewriting.
///
/// Rewriting can change literal identity or merge two rows. Presence is not
/// proof authority: every retained annotation must replay against the final
/// clause. Callers subsequently reconstruct missing certificates and demote any
/// arithmetic kind that remains uncertified.
pub(in crate::executor) fn sanitize_farkas_annotations(terms: &TermStore, proof: &mut Proof) {
    for step in &mut proof.steps {
        let ProofStep::TheoryLemma {
            clause,
            farkas,
            lia,
            ..
        } = step
        else {
            continue;
        };
        if farkas.as_ref().is_some_and(|annotation| {
            !certificate_valid_for_blocking_clause(terms, clause, annotation)
        }) {
            *farkas = None;
        }
        if matches!(
            lia.as_ref(),
            Some(ay_core::LiaAnnotation::CuttingPlane(cutting_plane))
                if !certificate_valid_for_blocking_clause(terms, clause, &cutting_plane.farkas)
        ) {
            *lia = None;
        }
    }
}
