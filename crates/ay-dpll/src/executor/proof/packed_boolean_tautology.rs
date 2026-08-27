// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lowering PACKED Boolean-tautology `trust` leaves to derivations.
//!
//! # The class this serves, as measured
//!
//! the development design notes measured the
//! corpus residual at this HEAD: of 757 premiseless `trust` steps, **110 in 3
//! files** are a single PACKED unit `(cl (or l1 .. ln))` whose FLAT clause
//! `(cl l1 .. ln)` is one of the strict checker's own Boolean tautology
//! schemas. Every one of the 110 is a two-atom equivalence over Boolean
//! operands that happen to be array reads, for example
//!
//! ```text
//! (cl (or (= (select a k) (= c k)) (not (select a k)) (not (= c k))))
//! ```
//!
//! which is `equiv_neg1` — `(cl (= X Y) (not X) (not Y))` — packed into one
//! disjunction. The array content is INCIDENTAL: `X` and `Y` are two Boolean
//! terms and the clause is a propositional tautology.
//!
//! # Why this is not a new authority
//!
//! Nothing here decides that a clause is a tautology. The lane never inspects
//! a shape of its own: for each candidate rule it hands the FLAT clause to the
//! UNTOUCHED `ay_proof::check_proof_strict` inside a self-contained refutation
//! and takes that answer, so the only schemas admitted are the ones the
//! mandatory gate already re-derives from the clause alone. A rule this file
//! names that the checker refuses simply never applies; a rule it fails to
//! name only costs completeness.
//!
//! # Why the leaf is RE-PACKED rather than flattened
//!
//! The leaf's consumers cite its clause. Emitting the flat clause would change
//! it and force every consumer to be re-justified. Instead the flat step is
//! extended by one premiseless `or_neg` and one `th_resolution` per disjunct
//! until the last clause is the packed unit again, byte for byte — the
//! construction `congruence_explanation_repack` already uses — so **no
//! consumer is touched at all**.
//!
//! # Guards
//!
//! 1. The leaf is a premiseless, argument-free `trust` step whose clause is a
//!    single `or` application.
//! 2. The FLAT clause is accepted by the untouched strict checker under a
//!    named rule, replayed as a closed refutation.
//! 3. The RE-PACKED fragment is closed and replayed by that same checker.
//! 4. The fragment's last clause is byte-identical to the leaf's.
//! 5. The fragment RENDERS under the export's own surface overrides.
//! 6. `commit_bridge_fragments` re-checks the WHOLE rebuilt proof and reverts
//!    wholesale if it does not check or if it costs a certification the
//!    original had.

use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId};
use ay_proof::CongruenceDerivation;

use super::super::Executor;

/// Largest number of packed leaves one call will plan for. The measured
/// per-proof population is 1-88; the cap only bounds a pathological proof.
const MAX_PACKED_TAUTOLOGY_LEAVES: usize = 512;

/// The premiseless, ARGUMENT-FREE Boolean tautology rules whose strict
/// validators decide a clause from the clause alone.
///
/// Membership is a COMPLETENESS list, never an authority: every entry is
/// handed to `check_proof_strict`, which is what actually accepts or refuses
/// it. Rules that need a premise (`not_and`, `not_equiv1`, ...) or an `:args`
/// payload (`and_pos`, `and_neg`) are deliberately absent — a bare step under
/// one of those cannot authenticate, and `PREMISE_OR_ARG_REQUIRED_ALETHE_RULES`
/// records that the pinned external checker rejects it too.
const PACKED_TAUTOLOGY_RULES: [AletheRule; 15] = [
    AletheRule::EquivPos1,
    AletheRule::EquivPos2,
    AletheRule::EquivNeg1,
    AletheRule::EquivNeg2,
    AletheRule::XorPos1,
    AletheRule::XorPos2,
    AletheRule::XorNeg1,
    AletheRule::XorNeg2,
    AletheRule::ItePos1,
    AletheRule::ItePos2,
    AletheRule::IteNeg1,
    AletheRule::IteNeg2,
    AletheRule::ImpliesPos,
    AletheRule::ImpliesNeg1,
    AletheRule::ImpliesNeg2,
];

/// Guard 1: the disjuncts of a premiseless, argument-free `trust` leaf whose
/// clause is a single PACKED `or` unit.
fn packed_tautology_candidate(terms: &ay_core::TermStore, step: &ProofStep) -> Option<Vec<TermId>> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    if !premises.is_empty() || !args.is_empty() {
        return None;
    }
    let [packed] = clause.as_slice() else {
        return None;
    };
    match terms.get(*packed) {
        TermData::App(ay_core::Symbol::Named(name), children) if name == "or" => {
            (children.len() >= 2).then(|| children.clone())
        }
        _ => None,
    }
}

impl Executor {
    /// Install the authored problem window a hand-built fixture refutes.
    ///
    /// Test-only: a real solve fills this from the frontend. A fixture that
    /// does not set it has a complete refutation whose every `assume` is
    /// unauthorized, which makes the whole-proof commit gate revert for a
    /// reason that has nothing to do with the guard under test.
    #[cfg(test)]
    pub(super) fn set_self_check_authored_assertions_for_tests(&mut self, assertions: Vec<TermId>) {
        self.self_check_authored_assertions = Some(assertions);
    }

    /// Lower every packed Boolean-tautology `trust` leaf to a derivation.
    ///
    /// Returns the number of leaves replaced.
    pub(in crate::executor) fn derive_packed_boolean_tautologies(
        &mut self,
        proof: &mut Proof,
    ) -> usize {
        let leaves: Vec<(usize, TermId, Vec<TermId>)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                let children = packed_tautology_candidate(&self.ctx.terms, step)?;
                let ProofStep::Step { clause, .. } = step else {
                    return None;
                };
                Some((index, *clause.first()?, children))
            })
            .take(MAX_PACKED_TAUTOLOGY_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_PACKED_TAUTOLOGY_LEAVES {
            return 0;
        }
        let overrides = self.last_proof_term_overrides.clone();
        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (index, packed, children) in leaves {
            let Some(fragment) = self.plan_packed_tautology_fragment(packed, &children) else {
                continue;
            };
            // Guard 5: a fragment that cannot be PUBLISHED is not planned.
            if self.bridge_fragment_is_unrenderable(&fragment, packed, overrides.as_ref()) {
                continue;
            }
            plans[index] = Some(fragment);
            planned += 1;
        }
        if planned == 0 {
            return 0;
        }
        self.commit_bridge_fragments(proof, plans)
    }

    /// The derivation for one packed leaf, or `None`.
    fn plan_packed_tautology_fragment(
        &mut self,
        packed: TermId,
        children: &[TermId],
    ) -> Option<Vec<ProofStep>> {
        // Guard 2: the UNTOUCHED strict checker names the rule, from the flat
        // clause alone, inside a self-contained refutation.
        let rule = self.strict_checked_tautology_rule(children)?;
        let flat = CongruenceDerivation {
            steps: vec![ProofStep::Step {
                rule,
                clause: children.to_vec(),
                premises: Vec::new(),
                args: Vec::new(),
            }],
            clause: children.to_vec(),
        };
        // Guard 4 is `repack_derivation`'s own postcondition: it returns `None`
        // unless its last clause is exactly `(cl packed)`.
        let repacked = self.repack_derivation(flat, packed)?;
        // Guard 3: the whole fragment is closed and replayed, so no step of it
        // enters the proof on this lane's word.
        let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &repacked);
        if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
            return None;
        }
        Some(repacked.steps)
    }

    /// Guard 2: the rule under which the UNTOUCHED strict checker accepts the
    /// FLAT clause, or `None` when it accepts none of them.
    ///
    /// The candidate is closed over the complement of each of its own literals
    /// so the checker sees a complete refutation and has to run the rule's real
    /// validator to accept it. Nothing about the clause is taken on this lane's
    /// word, and a rule whose validator refuses simply moves on to the next.
    fn strict_checked_tautology_rule(&mut self, children: &[TermId]) -> Option<AletheRule> {
        for rule in PACKED_TAUTOLOGY_RULES {
            let candidate = CongruenceDerivation {
                steps: vec![ProofStep::Step {
                    rule: rule.clone(),
                    clause: children.to_vec(),
                    premises: Vec::new(),
                    args: Vec::new(),
                }],
                clause: children.to_vec(),
            };
            let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &candidate);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_ok() {
                return Some(rule);
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "packed_boolean_tautology_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "packed_boolean_tautology_guard_tests.rs"]
mod guard_tests;
