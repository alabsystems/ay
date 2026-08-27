// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact rendered-surface exception for typed, OR-packed EUF transitivity.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Symbol, TermData, TermId};

use super::surface::{
    cone_mentions_key, is_exact_compositional_negation, is_exact_equality_swap,
    prepare_surface_map_bounded, PreparedSurfaceMap,
};
use super::EufLemmaPlan;
use crate::executor::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;
use crate::executor::Executor;

fn exact_packed_overrides_are_safe(
    terms: &ay_core::TermStore,
    prepared: &PreparedSurfaceMap,
) -> bool {
    for (&term, spelling) in &prepared.audited {
        match terms.get(term) {
            TermData::App(Symbol::Named(operator), sides)
                if operator == "=" && sides.len() == 2 =>
            {
                if !is_exact_equality_swap(terms, term, spelling, &prepared.canonical) {
                    return false;
                }
            }
            TermData::Not(inner)
                if matches!(
                    terms.get(*inner),
                    TermData::App(Symbol::Named(operator), sides)
                        if operator == "=" && sides.len() == 2
                ) && prepared.audited.contains_key(inner) =>
            {
                if !is_exact_compositional_negation(terms, term, spelling, &prepared.effective) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

fn exact_or_consumer_is_safe(
    terms: &ay_core::TermStore,
    plans: &[Option<EufLemmaPlan>],
    typed_packed: &[bool],
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> bool {
    let [premise] = premises else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let premise = premise.0 as usize;
    let Some(root) = typed_packed
        .get(premise)
        .copied()
        .filter(|is_typed| *is_typed)
        .and_then(|_| plans.get(premise))
        .and_then(Option::as_ref)
        .and_then(EufLemmaPlan::or_term)
    else {
        return false;
    };
    let TermData::App(Symbol::Named(operator), disjuncts) = terms.get(root) else {
        return false;
    };
    if operator != "or" || disjuncts.len() < 2 || clause.len() != disjuncts.len() {
        return false;
    }
    let mut actual = clause.to_vec();
    let mut expected = disjuncts.clone();
    actual.sort_unstable();
    expected.sort_unstable();
    actual == expected
}

enum CopiedRole {
    Safe,
    Roots(Vec<TermId>),
    Invalid,
}

fn copied_role(
    terms: &ay_core::TermStore,
    proof: &Proof,
    plans: &[Option<EufLemmaPlan>],
    typed_packed: &[bool],
    step: &ProofStep,
) -> CopiedRole {
    match step {
        ProofStep::Assume(_) | ProofStep::Resolution { .. } | ProofStep::Anchor { .. } => {
            CopiedRole::Safe
        }
        ProofStep::Step {
            rule: AletheRule::Contraction | AletheRule::Weakening,
            ..
        } => CopiedRole::Safe,
        ProofStep::Step {
            rule: AletheRule::Or,
            clause,
            premises,
            args,
        } => {
            if exact_or_consumer_is_safe(terms, plans, typed_packed, clause, premises, args) {
                CopiedRole::Safe
            } else {
                CopiedRole::Invalid
            }
        }
        ProofStep::Step {
            clause,
            premises,
            args,
            ..
        } => {
            let mut roots = clause.clone();
            roots.extend(args.iter().copied());
            for premise in premises {
                let Some(premise) = proof.steps.get(premise.0 as usize) else {
                    return CopiedRole::Invalid;
                };
                match premise {
                    ProofStep::Assume(term) => roots.push(*term),
                    ProofStep::Step { clause, .. }
                    | ProofStep::Resolution { clause, .. }
                    | ProofStep::TheoryLemma { clause, .. } => {
                        roots.extend(clause.iter().copied());
                    }
                    ProofStep::Anchor { .. } => {}
                    _ => return CopiedRole::Invalid,
                }
            }
            CopiedRole::Roots(roots)
        }
        ProofStep::TheoryLemma { clause, .. } => CopiedRole::Roots(clause.clone()),
        _ => CopiedRole::Invalid,
    }
}

fn copied_roles_are_safe(
    terms: &ay_core::TermStore,
    proof: &Proof,
    plans: &[Option<EufLemmaPlan>],
    typed_packed: &[bool],
    prepared: &PreparedSurfaceMap,
) -> bool {
    let mut work = 0usize;
    for (index, step) in proof.steps.iter().enumerate() {
        if typed_packed[index] {
            continue;
        }
        match copied_role(terms, proof, plans, typed_packed, step) {
            CopiedRole::Safe => {}
            CopiedRole::Roots(roots) => {
                if cone_mentions_key(terms, roots, &prepared.audited, &mut work) {
                    return false;
                }
            }
            CopiedRole::Invalid => return false,
        }
    }
    true
}

/// Select independently replannable generic leaves and exact typed OR-units.
pub(super) fn promotion_clause<'a>(
    terms: &ay_core::TermStore,
    step: &'a ProofStep,
) -> Option<(&'a [TermId], bool)> {
    match step {
        ProofStep::TheoryLemma {
            kind: ay_core::TheoryLemmaKind::Generic,
            clause,
            ..
        }
        | ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            ..
        } => Some((clause, false)),
        ProofStep::TheoryLemma { kind, clause, .. }
            if matches!(
                kind,
                ay_core::TheoryLemmaKind::EufTransitive | ay_core::TheoryLemmaKind::EufCongruent
            ) && matches!(
                clause.as_slice(),
                [unit]
                    if matches!(
                        terms.get(*unit),
                        TermData::App(symbol, arguments)
                            if symbol.name() == "or" && arguments.len() >= 2
                    )
            ) =>
        {
            Some((
                clause,
                matches!(kind, ay_core::TheoryLemmaKind::EufTransitive),
            ))
        }
        // The datatype ground-conflict CATCH-ALL is offered to the EUF planner
        // as well. Scoped to this one kind on purpose: it is the fallback that
        // fuses clauses no single-schema recognizer claimed, so it is the only
        // kind whose members are routinely not datatype reasoning at all.
        // Offering every `hole`-wired kind instead would put the planner in
        // front of genuine BV and datatype lemmas on every proof for no
        // expected gain, so the widening stays narrow.
        //
        // `infer_dt_lemma_kind`'s single-schema recognizers each accept ONE
        // shape, so a clause that mixes congruence with transitivity matches
        // none of them and falls through to the datatype ground-conflict
        // catch-all. That refuter closes it correctly — but `dt_ground_conflict`
        // has no rule in the pinned external calculus, so the step renders as
        // an honest `hole` and `unsat_proof_has_known_wire_gap` refuses the
        // whole verdict under `:check-proofs-strict`. The clause itself is
        // ordinary congruence + transitivity, both of which the external
        // checker DOES have rules for, so the right answer is to spell it in
        // those rules rather than to relax the wire policy.
        //
        // Offering it here is safe by construction: `plan_euf_lemma_with_budget`
        // must re-derive the clause from congruence closure alone, every
        // synthesized step is re-recognized, and the rebuilt proof is installed
        // only if the strict checker still accepts the whole document. A lemma
        // that is genuinely datatype-entailed (dt_distinct, dt_tester, ...) is
        // not EUF-entailed, so the planner declines and the step is copied
        // through byte-for-byte.
        ProofStep::TheoryLemma {
            kind: ay_core::TheoryLemmaKind::DatatypeGroundConflict,
            clause,
            ..
        } => Some((clause, false)),
        _ => None,
    }
}

pub(super) fn promotion_surfaces_are_safe(
    executor: &mut Executor,
    proof: &Proof,
    plans: &[Option<EufLemmaPlan>],
    typed_packed: &[bool],
) -> bool {
    if plans.len() != proof.steps.len() || typed_packed.len() != proof.steps.len() {
        return false;
    }
    let general = executor.generic_euf_promotion_surface_is_safe(proof, plans);
    let exact_typed = plans
        .iter()
        .enumerate()
        .all(|(index, plan)| plan.is_none() || typed_packed[index])
        && executor.typed_packed_euf_transitive_surface_is_safe(proof, plans, typed_packed);
    general || exact_typed
}

impl Executor {
    /// Narrow surface audit for already-certified, OR-packed
    /// `EufTransitive` units.
    ///
    /// The general promotion audit deliberately refuses an authored equality
    /// orientation that reaches a later `or` unpack. For this exact lane that
    /// orientation is harmless: `eq_transitive` accepts either equality
    /// orientation, generated `or_neg` and copied `or` render the same
    /// TermIds, and resolution is polarity-only. The exception admits only
    /// exact equality swaps plus their exact compositional negations, and only
    /// the exact one-premise `or` consumer of a replaced unit.
    pub(in crate::executor) fn typed_packed_euf_transitive_surface_is_safe(
        &self,
        proof: &Proof,
        plans: &[Option<EufLemmaPlan>],
        typed_packed: &[bool],
    ) -> bool {
        if plans.len() != proof.steps.len() || typed_packed.len() != proof.steps.len() {
            return false;
        }
        let Some(effective) = self.last_proof_term_overrides.as_ref() else {
            return true;
        };
        if effective.is_empty() {
            return true;
        }
        if !ProvenanceSurfaceAudit::default().active_map_is_bounded(effective) {
            return false;
        }
        let Some(prepared) = prepare_surface_map_bounded(&self.ctx.terms, effective, effective)
        else {
            return false;
        };
        prepared.audited.is_empty()
            || exact_packed_overrides_are_safe(&self.ctx.terms, &prepared)
                && copied_roles_are_safe(&self.ctx.terms, proof, plans, typed_packed, &prepared)
    }
}

#[cfg(test)]
#[path = "proof_euf_lemma_packed_surface_tests.rs"]
mod tests;
