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
    ay_core::proof_validation::verify_farkas_conflict_lits_full_holds(
        terms,
        &blocking_clause_to_conflict(terms, clause),
        farkas,
    )
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

/// The atom and asserted polarity of a conflict literal, with every surface
/// `not` unwrapped — the same normalization
/// [`ay_core::proof_validation::conflict_lits_satisfied_by`] performs, so the
/// LRA solver is asked about the atom the verifier will parse.
fn asserted_atom(terms: &TermStore, literal: &ay_core::TheoryLit) -> (TermId, bool) {
    let mut term = literal.term;
    let mut value = literal.value;
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }
    (term, value)
}

/// Whether a MODEL of `clause`'s negation exists AND has been verified here.
///
/// `clause` is a blocking clause, so its negation is the conjunction of the
/// asserted literals. When this returns `true`, no sub-multiset of those
/// literals admits a Farkas certificate that
/// [`certificate_valid_for_blocking_clause`] would accept: the model satisfies
/// every row, and every accept path needs a weighted combination of rows to be
/// contradictory. A producer searching bounded SUBSETS of a fixed literal pool
/// can therefore decide the whole search with this ONE call instead of
/// enumerating it.
///
/// The LRA solver is a HINT source and is granted no authority. It supplies
/// candidate values — which is why any non-`Unsat` verdict is taken, including
/// the combined-theory `NeedModelEquality`/`NeedSplit` interface requests that
/// carry a simplex assignment without a final verdict — and
/// [`ay_core::proof_validation::conflict_lits_satisfied_by`] then re-derives
/// the verifier's own rows and checks every one of them by evaluation. A solver
/// that answered wrongly, or a rational assignment that does not satisfy the
/// integer strengthening the verifier applies, is rejected here and the caller
/// falls back to its unpruned search. Fail-closed in both directions.
pub(in crate::executor) fn blocking_clause_negation_has_verified_model(
    terms: &TermStore,
    clause: &[TermId],
) -> bool {
    let conflict = blocking_clause_to_conflict(terms, clause);
    let mut lra = ay_lra::LraSolver::new(terms);
    lra.set_combined_theory_mode(true);
    for literal in &conflict {
        let (atom, _) = asserted_atom(terms, literal);
        ay_core::TheorySolver::register_atom(&mut lra, atom);
    }
    for literal in &conflict {
        let (atom, value) = asserted_atom(terms, literal);
        ay_core::TheorySolver::assert_literal(&mut lra, atom, value);
    }
    if matches!(
        ay_core::TheorySolver::check(&mut lra),
        ay_core::TheoryResult::Unsat(_) | ay_core::TheoryResult::UnsatWithFarkas(_)
    ) {
        return false;
    }
    ay_core::proof_validation::conflict_lits_satisfied_by(terms, &conflict, &|term| {
        lra.get_value(term)
    })
}
