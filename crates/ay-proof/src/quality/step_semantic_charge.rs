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
    // `array_ext_diff_intro` belongs here too: it is a DEFINITION whose
    // per-step validator (`array_axiom::validate_ext_diff_intro`) is arity
    // guards, one `terms.get` on the witness, four sort reads, two `TermId`
    // comparisons and a name clone — O(1) over its three arguments. Its
    // whole-proof conditions (fresh, bound once, acyclic) live in
    // `ExtDiffRegistry::collect`, charged separately by
    // `ext_diff_registry_charge`. Under `General` one such step precharged
    // `33068^2 = 1_093_492_624` — 3.1x the whole envelope — on
    // `QF_AX/swap/swap_t2_np_nf_ai_00008_008` (measured with
    // `--probe-strict-check`), refusing a walk on a definition that reads
    // three arguments.
    matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Reordering
                | AletheRule::Weakening
                | AletheRule::EqReflexive
                | AletheRule::ArrayExtDiffIntro,
            ..
        }
    )
}

pub(super) fn strict_semantic_charge(
    step: &ProofStep,
    semantic_payload: PayloadStats,
    semantic_class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology,
            ..
        }
    ) {
        // `prepare_strict_bv_session` prepays every BV/LIA lemma before any
        // step is validated. Its census reserves the bounded source
        // interpreter's complete work/byte maxima (or the separately bounded
        // closed-constant case), including repeated lemmas. The validator
        // still re-derives UNSAT from the exact recovered source roots.
        // Authentication and this step's structural charge cover the clause
        // and explicit-negation wrapper. A General unfolded-payload product
        // here would reserve a second, unrelated interpreter on top of that
        // complete reservation: 894M extra work on the 849-root TY query.
        return Ok((0, 0));
    }
    if matches!(
        step,
        ProofStep::NraSos { .. } | ProofStep::FiniteFieldLinear { .. }
    ) {
        // Native SOS replay debits its actual polynomial and rational work
        // through this validation's callback. Authentication already charged
        // every payload vector, integer limb, and embedded term root.
        return Ok((0, 0));
    }
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
