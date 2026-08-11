// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas coefficient synthesis and reconstruction for theory lemma proofs.
//!
//! Extracted from `proof.rs` as part of #6763.

use ay_core::term::TermData;
use ay_core::{Proof, ProofStep, Symbol, TheoryLemmaKind};
use ay_core::{TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;

pub(in crate::executor) use super::proof_farkas_synthesis::{
    synthesize_equality_farkas, synthesize_mixed_equality_arithmetic_farkas,
};
use super::proof_farkas_validation::certificate_valid_for_blocking_clause;
use super::proof_surface_syntax::strip_frontend_annotations;

/// Reconstruct missing Farkas coefficients for arithmetic theory lemmas (#6757).
///
/// The post-rewrite promotion pass (`promote_generic_theory_lemma_kinds_after_rewrite`)
/// only handles trust-kind lemmas. Lemmas that are already `LiaGeneric` or
/// `LraFarkas` (from the theory solver) but lack Farkas coefficients are not
/// promoted — they need a separate reconstruction pass.
///
/// For each qualifying lemma: tries LRA solver first, then equality synthesis.
pub(crate) fn reconstruct_missing_farkas_coefficients(
    terms: &mut TermStore,
    proof: &mut Proof,
    assertions: &[TermId],
    hidden_equality_assertions: &[TermId],
) {
    // Collect equality assertions for clause unsimplification (#6757).
    // Combined-theory conflicts may record the linking equality as
    // `Not(true)` when the assertion was simplified at the SAT level.
    // The original assertion TermIds in ctx.assertions have the
    // un-simplified equality.
    let true_id = terms.true_term();
    let equality_assertions: Vec<TermId> = assertions
        .iter()
        .copied()
        .filter(|&term| {
            matches!(
                terms.get(term),
                TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
            )
        })
        .collect();
    let mut equality_assertions = equality_assertions;
    for &term in hidden_equality_assertions {
        if !equality_assertions.contains(&term) {
            equality_assertions.push(term);
        }
    }
    // (#6759) Also scan proof Assume steps for equality terms. In the
    // with_deferred_postprocessing path, provenance-aware assertions may
    // include equalities not present in ctx.assertions (which holds
    // simplified forms).
    for step in proof.steps.iter() {
        if let ProofStep::Assume(term) = step {
            if !equality_assertions.contains(term)
                && matches!(
                    terms.get(*term),
                    TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
                )
            {
                equality_assertions.push(*term);
            }
        }
    }

    for step in &mut proof.steps {
        let ProofStep::TheoryLemma {
            kind,
            clause,
            farkas,
            ..
        } = step
        else {
            continue;
        };
        if farkas.is_some() {
            continue;
        }
        // Skip non-arithmetic theory lemma kinds that can never produce
        // Farkas coefficients (BV bit-blasting, pure EUF congruence).
        if matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
                | TheoryLemmaKind::BvBitBlastGate { .. }
                | TheoryLemmaKind::ArraySelectStore { .. }
                | TheoryLemmaKind::ArrayStorePermutation
                | TheoryLemmaKind::ArrayRowChain
                | TheoryLemmaKind::ArrayExtensionality
                | TheoryLemmaKind::FpToBv { .. }
                | TheoryLemmaKind::StringLengthAxiom
                | TheoryLemmaKind::StringContentAxiom
                | TheoryLemmaKind::StringNormalForm
                | TheoryLemmaKind::StringGroundEval
                | TheoryLemmaKind::RegexIntersectEmpty
                | TheoryLemmaKind::EufTransitive
                | TheoryLemmaKind::EufReflexive
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufCongruentPred
        ) {
            continue;
        }

        if try_lra_farkas_reconstruction(terms, clause, farkas, kind) {
            continue;
        }

        // (#6757) If the clause contains `Not(true)` from a simplified
        // linking equality, try replacing it with each equality assumption
        // and re-attempting Farkas reconstruction.
        let simplified_positions: Vec<usize> = clause
            .iter()
            .enumerate()
            .filter_map(|(i, &lit)| match terms.get(lit) {
                TermData::Not(inner) if *inner == true_id => Some(i),
                _ => None,
            })
            .collect();
        if !simplified_positions.is_empty() {
            let original_clause = clause.clone();
            for &eq_term in &equality_assertions {
                // Create Not(eq_term) in the term store (#6757). The
                // negation may not exist yet because the clause was built
                // with Not(true) when EUF simplified the equality.
                let neg_eq = terms.mk_not_raw(eq_term);
                let mut candidate_clause = original_clause.clone();
                for &pos in &simplified_positions {
                    candidate_clause[pos] = neg_eq;
                }
                let mut candidate_farkas = None;
                let mut candidate_kind = *kind;
                if try_lra_farkas_reconstruction(
                    terms,
                    &candidate_clause,
                    &mut candidate_farkas,
                    &mut candidate_kind,
                ) {
                    // Reconstruction proved the unsimplified replacement, but
                    // the proof step still publishes `clause`. Commit neither
                    // certificate nor kind until the exact published clause
                    // independently accepts it.
                    if let Some(candidate_farkas) = candidate_farkas.filter(|candidate| {
                        certificate_valid_for_blocking_clause(terms, clause, candidate)
                    }) {
                        *farkas = Some(candidate_farkas);
                        *kind = candidate_kind;
                        break;
                    }
                }
                // (#6759) If pure Farkas failed, try mixed equality+arithmetic
                // synthesis on the unsimplified candidate clause.
                if let Some(synth) =
                    synthesize_mixed_equality_arithmetic_farkas(terms, &candidate_clause)
                {
                    // The proof step still contains `clause`, not the
                    // unsimplified candidate. Never attach a certificate proved
                    // only for the replacement shape (#6759): it must replay
                    // against the exact clause that will be published.
                    if certificate_valid_for_blocking_clause(terms, clause, &synth) {
                        *farkas = Some(synth);
                        if kind.is_trust() || matches!(kind, TheoryLemmaKind::Generic) {
                            *kind = TheoryLemmaKind::LiaGeneric;
                        }
                        break;
                    }
                }
            }
            if farkas.is_some() {
                continue;
            }
        }

        // Fallback: equality synthesis for (= t c1) vs (= t c2) patterns.
        if let Some(synth) = synthesize_equality_farkas(terms, clause)
            .filter(|candidate| certificate_valid_for_blocking_clause(terms, clause, candidate))
        {
            *farkas = Some(synth);
            if kind.is_trust() {
                *kind = TheoryLemmaKind::LiaGeneric;
            }
            continue;
        }

        // Fallback: mixed equality + arithmetic synthesis (#6759).
        // For clauses with one equality and arithmetic literals, substitute
        // equal terms to get a pure arithmetic clause, then run Farkas.
        if let Some(synth) = synthesize_mixed_equality_arithmetic_farkas(terms, clause)
            .filter(|candidate| certificate_valid_for_blocking_clause(terms, clause, candidate))
        {
            *farkas = Some(synth);
            if kind.is_trust() {
                *kind = TheoryLemmaKind::LiaGeneric;
            }
        }
    }
}

/// Check if a frontend term is an equality application.
pub(crate) fn frontend_term_is_equality(term: &FrontendTerm) -> bool {
    matches!(
        strip_frontend_annotations(term),
        FrontendTerm::App(name, args) if name == "=" && args.len() == 2
    )
}

/// Try to reconstruct Farkas coefficients for a single theory lemma clause
/// using the LRA solver. Returns true if successful.
pub(crate) fn try_lra_farkas_reconstruction(
    terms: &TermStore,
    clause: &[TermId],
    farkas: &mut Option<ay_core::FarkasAnnotation>,
    kind: &mut TheoryLemmaKind,
) -> bool {
    let mut lra = ay_lra::LraSolver::new(terms);
    lra.set_combined_theory_mode(true);
    for &lit in clause.iter() {
        let atom = match terms.get(lit) {
            TermData::Not(inner) => *inner,
            _ => lit,
        };
        ay_core::TheorySolver::register_atom(&mut lra, atom);
    }
    for &lit in clause.iter() {
        let (atom, value) = match terms.get(lit) {
            TermData::Not(inner) => (*inner, true),
            _ => (lit, false),
        };
        ay_core::TheorySolver::assert_literal(&mut lra, atom, value);
    }
    let ay_core::TheoryResult::UnsatWithFarkas(conflict) = ay_core::TheorySolver::check(&mut lra)
    else {
        return false;
    };
    let Some(source_farkas) = conflict.farkas.as_ref() else {
        return false;
    };
    if source_farkas.coefficients.len() != conflict.literals.len() {
        return false;
    }

    // LraSolver returns coefficients in `conflict.literals` order, which is
    // free to differ from registration/assertion order. Recover the exact
    // blocking-clause identity of each row, then rebind by TermId. Attaching
    // this vector directly to `clause` is unsound after a solver permutation.
    let zero = num_rational::Rational64::from(0);
    let mut source_clause = Vec::with_capacity(conflict.literals.len());
    let mut source_coefficients = Vec::with_capacity(conflict.literals.len());
    for (&literal, coefficient) in conflict
        .literals
        .iter()
        .zip(source_farkas.coefficients.iter())
    {
        let blocker = clause.iter().copied().find(|&candidate| {
            if literal.value {
                matches!(terms.get(candidate), TermData::Not(inner) if *inner == literal.term)
            } else {
                candidate == literal.term
            }
        });
        match blocker {
            Some(blocker) => {
                source_clause.push(blocker);
                source_coefficients.push(*coefficient);
            }
            None if *coefficient == zero => {}
            None => return false,
        }
    }
    let source_farkas = ay_core::FarkasAnnotation::new(source_coefficients);
    let Some(rebound) = source_farkas.rebind_by_literal(&source_clause, clause) else {
        return false;
    };
    if !rebound.is_valid() {
        return false;
    }

    // Re-check the rebound certificate against the exact target clause before
    // it can become proof authority. This is independent of the producing LRA
    // solver and catches every remaining polarity/order mismatch fail-closed.
    let target_conflict: Vec<ay_core::TheoryLit> = clause
        .iter()
        .map(|&literal| match terms.get(literal) {
            TermData::Not(inner) => ay_core::TheoryLit::new(*inner, true),
            _ => ay_core::TheoryLit::new(literal, false),
        })
        .collect();
    if ay_core::proof_validation::verify_farkas_conflict_lits_full(
        terms,
        &target_conflict,
        &rebound,
    )
    .is_err()
    {
        return false;
    }

    let inferred_kind =
        crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
            terms,
            clause,
            Some(&rebound),
        );
    *farkas = Some(rebound);
    *kind = if inferred_kind.is_trust() {
        TheoryLemmaKind::LraFarkas
    } else {
        inferred_kind
    };
    true
}
