// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic replay charges that depend on a proof step's validation route.

use super::*;

pub(super) fn is_euf_identity_route(step: &ProofStep) -> bool {
    matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Refl
                | AletheRule::Symm
                | AletheRule::Trans
                | AletheRule::Cong
                | AletheRule::EqTransitive
                | AletheRule::EqCongruent
                | AletheRule::EqCongruentPred,
            ..
        } | ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufReflexive
                | TheoryLemmaKind::EufTransitive
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufCongruentPred,
            ..
        }
    )
}

/// Recognize the syntax-only clause-identity rules whose strict validators read
/// clause literals as opaque `TermId`s and never descend into one.
///
/// This grants no proof authority and it is deliberately NARROW. `contraction`
/// is NOT here: its validator is quadratic in the clause length by three
/// nested `contains` scans, which the `General` product already models with
/// the right SHAPE. Add a rule only when its strict validator provably touches
/// no subterm — check the validator, not the rule's name.
pub(super) fn is_clause_identity_route(step: &ProofStep) -> bool {
    matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Reordering | AletheRule::Weakening | AletheRule::EqReflexive,
            ..
        }
    )
}

pub(super) fn strict_semantic_charge(
    step: &ProofStep,
    semantic_payload: PayloadStats,
    semantic_class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    // `ArrayRowChain` AND `ArrayStorePermutation` meter their ACTUAL validation
    // work through the strict-check progress callback inside their validators
    // ([`crate::checker::validate_array_row_chain`] /
    // [`crate::checker::validate_array_store_permutation`]) — the same
    // (0,0)-precharge-then-debit-actual pattern `ResolutionRoute`/`Generic`
    // lemmas use — so they take NO up-front semantic precharge here. The former
    // `ArrayClauseSchema` precharge (`~8 * unfolded_work^2`) is quadratic in the
    // step's unfolded payload, hence QUARTIC in the store-chain length for the
    // store-commutativity clause shape (whose `O(P^2)` index-pair literal count
    // makes `unfolded_work` itself `Θ(P^2)`); it over-charged the common
    // genuinely-`O(L + P^2)` shape and withheld a correctly decided `storecomm`
    // UNSAT. Both validators now debit a tight `O(L + P^2)` bound per node/pair
    // and fail closed on an adversarial clause.
    //
    // `EufCongruenceExplanation` joins them for the same reason and by the same
    // mechanism: `crate::checker::validate_euf_congruence_explanation` debits
    // every interned node and every fixpoint node-visit through THIS callback.
    // Its population is the packed QF_AX congruence explanations, whose literals
    // share one deep `store` chain — precisely the shape where the `General`
    // `unfolded_work^2` precharge exceeds the whole envelope and would turn a
    // typed `TrustStep` refusal into a `ResourceLimit` one.
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain
                | TheoryLemmaKind::ArrayStorePermutation
                | TheoryLemmaKind::EufCongruenceExplanation,
            ..
        }
    ) {
        Ok((0, 0))
    } else if matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Hole | AletheRule::Trust,
            ..
        }
    ) {
        // A hole/trust step has NO semantic validator to reserve for: the
        // strict checker rejects it in O(1) with the typed
        // `HoleStep`/`TrustStep` refusal, and the non-strict lanes skip it.
        // Billing the General tree-unfolded estimate here charged a single
        // 1000-literal hole 285M+ work — exhausting the whole envelope and
        // masking the TYPED refusal (`ResourceLimit` instead of `HoleStep`),
        // which starves every downstream repair lane keyed on that reason.
        // The structural per-step charge in `strict_step_charge` still
        // applies, so an adversarial million-hole document remains bounded.
        Ok((0, 0))
    } else {
        semantic_validator_charge(step, semantic_payload, semantic_class)
    }
}
