// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical proof shape and serialized exact-query identity checks.

use super::*;
use ay_core::{ProofId, ProofStep, Sort, TermStore};

/// Compare the complete positional arena without cloning its payloads.
/// Unused entries remain part of the sealed bundle's exact identity.
fn term_entries_match(terms: &TermStore, entries: &[(TermData, Sort)]) -> bool {
    terms.len() == entries.len()
        && terms
            .term_ids()
            .map(|id| (terms.get(id), terms.sort(id)))
            .eq(entries.iter().map(|(term, sort)| (term, sort)))
}

fn proof_roots_match_exact_query(
    executor: &Executor,
    exact_roots: &[TermId],
    proof_roots: &[TermId],
) -> bool {
    crate::executor::proof_original_rebuild::collect_bounded_bv_lia_roots(
        &executor.ctx.terms,
        exact_roots,
    )
    .is_some_and(|expected| expected == proof_roots)
}

/// Lock the wire-gap exception to the sole canonical proof constructor.
///
/// This intentionally checks every step, including unreachable ones: a future
/// producer cannot inherit the exception by appending a second native-only
/// rule to an otherwise valid BV/LIA refutation.
pub(super) fn canonical_bv_lia_proof_matches(
    executor: &Executor,
    proof: &Proof,
    proof_roots: &[TermId],
) -> bool {
    let root_count = proof_roots.len();
    if root_count == 0
        || !proof.named_steps.is_empty()
        || proof.steps.len() != root_count.saturating_mul(2).saturating_add(1)
    {
        return false;
    }
    for (index, &root) in proof_roots.iter().enumerate() {
        if !matches!(proof.steps.get(index), Some(ProofStep::Assume(actual)) if *actual == root) {
            return false;
        }
    }

    let Some(ProofStep::TheoryLemma {
        theory,
        clause,
        farkas,
        kind,
        lia,
    }) = proof.steps.get(root_count)
    else {
        return false;
    };
    if theory != "BV_LIA"
        || farkas.is_some()
        || *kind != TheoryLemmaKind::BvLiaTautology
        || lia.is_some()
        || clause.len() != root_count
    {
        return false;
    }
    for (&literal, &root) in clause.iter().zip(proof_roots) {
        if executor.ctx.terms.entry_stamp(literal).is_none()
            || !matches!(executor.ctx.terms.get(literal), TermData::Not(inner) if *inner == root)
        {
            return false;
        }
    }

    let Ok(theory_step) = u32::try_from(root_count) else {
        return false;
    };
    for (index, &root) in proof_roots.iter().enumerate() {
        let Some(ProofStep::Resolution {
            clause: residual,
            pivot,
            clause1,
            clause2,
        }) = proof.steps.get(root_count + 1 + index)
        else {
            return false;
        };
        let Ok(assume_step) = u32::try_from(index) else {
            return false;
        };
        let Ok(previous_step) = u32::try_from(root_count + index) else {
            return false;
        };
        if residual.as_slice() != &clause[index + 1..]
            || *pivot != root
            || *clause1
                != ProofId(if index == 0 {
                    theory_step
                } else {
                    previous_step
                })
            || *clause2 != ProofId(assume_step)
        {
            return false;
        }
    }
    true
}

impl Executor {
    /// Whether an exact root is the canonical `false` without a literal
    /// `false` authored for it — the one root this lane's canonical proof
    /// cannot assume.
    ///
    /// A public root that ELABORATED to the canonical `false` refutes the query
    /// by itself, and this lane cannot certify that refutation: its native
    /// certificate assumes every exact root verbatim, while the strict premise
    /// scope admits `false` only where the author literally wrote it
    /// (`boolean_constant_premises_authored`). `(< (- 8 1) 0)` and
    /// `(= (bvadd #x01 #x01) #x03)` fold onto the same canonical term without
    /// spelling it, so the bundle's `(assume false)` was rejected ("assumes term
    /// t1 outside the supplied problem obligation") and a correct `unsat` was
    /// withdrawn to `unknown (incomplete self-check-rejected)` on every such
    /// query that also mentions `bv2nat`/`int2bv` — a split-conjunct VC whose
    /// violation constant-folds is exactly that shape. No bundle is minted for
    /// such roots; the query's refutation is the folded root alone, certified
    /// from its authored surface by the ordinary proof reconstruction (the
    /// false-collapse repair). A literally authored `false` is an authorized
    /// premise and keeps the lane.
    pub(super) fn exact_roots_hold_unauthored_false(&self, exact_roots: &[TermId]) -> bool {
        exact_roots.contains(&self.ctx.terms.false_term())
            && !self.boolean_constant_premises_authored().1
    }

    /// [`Self::exact_roots_hold_unauthored_false`] over the PUBLIC query: the
    /// epoch's assertions plus `assumptions`. `false` there refutes the public
    /// query outright, whatever transient window a route is solving.
    pub(in crate::executor) fn public_roots_hold_unauthored_false(
        &self,
        assumptions: &[TermId],
    ) -> bool {
        let false_term = self.ctx.terms.false_term();
        self.unsat_query_epoch.as_ref().is_some_and(|epoch| {
            epoch.assertions.contains(&false_term) || assumptions.contains(&false_term)
        }) && !self.boolean_constant_premises_authored().1
    }
}

pub(super) fn bundle_matches_proof(
    executor: &Executor,
    exact_roots: &[TermId],
    proof_roots: &[TermId],
    proof: &Proof,
    bundle: &SerializableProofBundle,
) -> bool {
    proof_roots_match_exact_query(executor, exact_roots, proof_roots)
        && canonical_bv_lia_proof_matches(executor, proof, proof_roots)
        && proof.steps == bundle.steps
        && bundle.obligation_assertions == exact_roots
        && term_entries_match(&executor.ctx.terms, &bundle.term_entries)
        && bundle.true_term == Some(executor.ctx.terms.true_term())
        && bundle.false_term == Some(executor.ctx.terms.false_term())
        && bundle.var_counter == executor.ctx.terms.var_counter()
        && bundle.datatype_declarations.is_empty()
        && bundle.constructor_selectors.is_empty()
        && bundle.datatype_member_signatures.is_empty()
}

pub(super) fn bundle_matches_live_proof(
    executor: &Executor,
    exact_roots: &[TermId],
    proof_roots: &[TermId],
    bundle: &SerializableProofBundle,
) -> bool {
    executor.last_proof.as_ref().is_some_and(|proof| {
        bundle_matches_proof(executor, exact_roots, proof_roots, proof, bundle)
    })
}

#[cfg(test)]
mod tests;
