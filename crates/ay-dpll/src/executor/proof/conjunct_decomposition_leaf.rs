// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive an `and`-headed premiseless `trust` leaf CONJUNCT BY CONJUNCT, when
//! the whole-term congruence route cannot reach it.
//!
//! # The residual this lane owns, and why the whole-term route cannot take it
//!
//! [`super::minted_definition_leaf`] closes an `and`-headed leaf by aligning it
//! against an AUTHORED root, MINTING the definition of every fresh symbol the
//! rewrite introduced, and explaining the whole leaf with ONE congruence. That
//! works for 6 of 34 measured leaves. The other 28 (26 after that lane ships)
//! differ from their authored counterpart at a position underneath a
//! `TermData::Not`, and `ay_proof::congruence_forest` descends only
//! `TermData::App` — deliberately, because `eq_congruent`'s validator requires
//! BOTH sides of its conclusion to be `App` with the same symbol, so a `Not`
//! congruence could not be lowered.
//!
//! The way past that is not a wider congruence. It is to stop asking for one
//! equality over the whole conjunction and ask for `n` SMALLER ones, because
//! `TermStore::mk_eq` LIFTS a Boolean equality between two negations:
//! `mk_eq((not X'), (not X))` is `(= X' X)`, whose two sides ARE `App`-headed.
//! The `not` that blocks the whole-term congruence disappears at the conjunct
//! level, and `equiv_pos1`/`equiv_pos2` turns `(= X' X)` plus `(not X')` into
//! `(not X)` with no new checker capability at all.
//!
//! # What replaces the leaf
//!
//! ```text
//!  before                              after
//!  i: (cl (and g_1 .. g_n))  trust     assume ROOT = (and a_1 .. a_n)
//!                                      per UNCHANGED conjunct  (g_i = a_i):
//!                                        (cl (not ROOT) a_i)   and_pos i
//!                                        (cl a_i)              th_resolution
//!                                      per CHANGED conjunct:
//!                                        (cl (not ROOT) a_i)   and_pos i
//!                                        (cl a_i)              th_resolution
//!                                        the minted definitions + congruence
//!                                        (cl (= a_i g_i))      th_resolution
//!                                        (cl ¬(= a_i g_i) ā_i g_i)  equiv_pos*
//!                                        (cl ā_i g_i)          th_resolution
//!                                        (cl g_i)              th_resolution
//!                                      (cl (and g..) ḡ_1 .. ḡ_n)  and_neg
//!                                      (cl (and g_1 .. g_n))   th_resolution
//! ```
//!
//! `ā` / `ḡ` are SYNTACTIC complements
//! ([`super::minted_definition_leaf::syntactic_complement`]), not `mk_not`:
//! `mk_not` returns the De Morgan dual for an `and`/`or` literal, which is
//! Boolean-equivalent but not a resolution complement.
//!
//! The last step's clause is byte-identical to the `trust` step's, so every
//! downstream premise reference, resolution and pivot sees exactly the clause
//! it saw before.
//!
//! # Metering — MEASURED, and it is not the obstacle
//!
//! The 2026-08-23 census doc suspected `and_neg`'s
//! `SemanticChargeClass::General` precharge — quadratic in the TREE-unfolded
//! step payload — of being the blocker on a 29-conjunct leaf. Measured on this
//! machine with a temporary probe over the REAL metering walk
//! (`ay_proof`'s `meter_step_term_payload`), on the exact leaves this lane
//! serves:
//!
//! | file | n | `work` | `unfolded_work` | `General` precharge | of the 350 M envelope |
//! |---|---|---|---|---|---|
//! | `clearsy_0001_00310_falsesat44` | 29 | 2 134 | 303 | **646 602** | 0.18% |
//! | `clearsy_0000_00307_falsesat13` | 22 | 1 770 | 245 | **433 650** | 0.12% |
//!
//! These are QF_UF conjunctions of small equalities: the tree unfolding is a
//! few hundred nodes, not a few hundred thousand, so the square of it is
//! negligible against the envelope. NO charge model was changed for this lane,
//! and none is justified: `validate_and_neg` READS SUBTERMS — through
//! `matches_negation_of_term`, which recurses De Morgan, `Ite` and
//! double-negation shapes with no memo table — so its worst case really is
//! quadratic in the tree unfolding and `General` already models it with the
//! right SHAPE. See `ay_proof`'s `metering_and_neg` tests, which pin both the
//! bound and the exponential-unfolding counterexample.
//!
//! # Authority
//!
//! Exactly the two authorities the sibling lanes already carry, and no third:
//!
//! * the only term ASSUMED is `ROOT`, an authored assertion in the
//!   INTERSECTION of the scope this rewrite was handed and the scope the
//!   strict presentation checks against (the sibling lanes' Guard 3). No
//!   conjunct is ever assumed — `validate_reachable_assumes_in_problem_scope`
//!   admits only EXACT membership, so an assumed conjunct would be an
//!   authority the strict presentation takes on faith;
//! * the minted `fresh_def_eq` definitions, whose soundness is the
//!   conservative definitional-extension argument
//!   [`ay_proof::FreshDefRegistry`] already carries and which the UNTOUCHED
//!   checker re-decides over the finished proof — FRESH, INDEPENDENT, SORT and
//!   SINGLE DEFINIENS — plus this lane's Gate 2.
//!
//! Every other step is a premise-free tautology the checker decides from the
//! clause alone (`and_pos`, `and_neg`, `equiv_pos1`/`equiv_pos2`,
//! `eq_congruent`, `eq_reflexive`, `eq_transitive`) or a resolution decided
//! from its premises.
//!
//! # Guards
//!
//! Each is mutation-checked in `conjunct_decomposition_leaf_guard_tests.rs`.
//!
//! 1. **No `Anchor` steps** — their forward references the in-order remap
//!    cannot resolve.
//! 2. **A premiseless, argument-free `trust` step whose unit clause is an
//!    `and` application of at least two conjuncts.**
//! 3. **The ROOT is in BOTH authored scopes**, is an `and` application, and
//!    has the SAME ARITY as the leaf.
//! 4. **The root is not the leaf itself.** A decomposition with nothing to
//!    explain would replace a `trust` step with a longer proof that says the
//!    same thing. `TermStore` HASH-CONSES, so two `and` applications with the
//!    same argument list are the same term: the `root == atom` skip therefore
//!    already decides "at least one conjunct differs", and a separate
//!    conjunct-wise test is dead code (measured — deleting one failed nothing,
//!    so it is not carried).
//! 5. **Every differing conjunct's definitions are minted under the
//!    minted-definition lane's OWN vetting**, over the alignment of the WHOLE
//!    leaf against the WHOLE root — which descends `Not` as well as `App`, so
//!    the single-definiens decision is taken once across the leaf rather than
//!    per conjunct.
//! 6. **Every per-conjunct congruence derivation strict-checks** on its own,
//!    closed, and the propositional rule is CHOSEN by the checker.
//! 7. **The `and_neg` step strict-checks** on its own, closed — the checker's
//!    `validate_and_neg`, not this lane, decides that the complement literals
//!    bijectively cover the conjuncts.
//! 8. **The fragment ends on exactly the leaf's clause**, byte for byte.
//! 9. **The fragment RENDERS** under the export's own surface overrides.
//! 10. **Gate 2** — after the splice, the checker's own
//!     [`ay_proof::FreshDefRegistry::collect`] over the WHOLE proof against the
//!     UNION of both authored scopes, reverting the entire rewrite on any
//!     decline. `commit_bridge_fragments`' backstop is not sufficient on its
//!     own: a non-fresh definition turns a RESCUABLE `TrustStep` rejection into
//!     a HARD `InvalidTheoryLemma` one, which the backstop cannot catch because
//!     the original did not certify either.

use ay_core::kani_compat::DetHashSet;
use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId};

use super::super::Executor;
use super::minted_definition_leaf::{MintContext, Minted, MAX_ALIGN_NODES, MAX_MINTED_PER_LEAF};

/// Largest number of `trust` leaves one call will plan for. Mirrors the
/// sibling lanes' cap; the measured per-proof population is 13.
const MAX_DECOMPOSED_LEAVES: usize = 512;

/// Largest number of AUTHORED roots one leaf is tried against. Mirrors the
/// minted-definition lane's cap.
const MAX_DECOMPOSED_ROOTS_PER_LEAF: usize = 64;

/// Largest conjunction this lane will decompose. Every conjunct costs one
/// `and_pos` pair and one clause literal, so this bounds the fragment an
/// adversarial leaf can force. The measured population is 20-29.
pub(super) const MAX_DECOMPOSED_CONJUNCTS: usize = 256;

/// Whether `step` is a leaf this lane may replace (Guard 2).
pub(super) fn is_decomposition_candidate(
    terms: &ay_core::TermStore,
    step: &ProofStep,
) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    if !premises.is_empty() || !args.is_empty() || clause.len() != 1 {
        return None;
    }
    let atom = clause[0];
    (conjunction_children(terms, atom)?.len() >= 2).then_some(atom)
}

/// The arguments of `term` when it is an `and` application.
pub(super) fn conjunction_children(terms: &ay_core::TermStore, term: TermId) -> Option<&[TermId]> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "and" => Some(args),
        _ => None,
    }
}

/// Align `leaf` against `root`, descending same-symbol/same-arity `App` nodes
/// AND `Not` nodes, recording one `(leaf sub-term, root sub-term)` pair per
/// differing position. Returns `false` when the budget is exhausted.
///
/// This is [`super::minted_definition_leaf::align`] with the `Not` descent
/// ADDED, and the difference is exactly what this lane exists for. The sibling
/// alignment stops AT a `Not` and records the whole `Not` node as the differing
/// position, because its consumer is a whole-term congruence that cannot
/// descend one. This lane's consumer is a PER-CONJUNCT congruence over
/// `mk_eq`'s lifted equality, which never has to descend a `Not` at all — so
/// the alignment may, and must, look through it to find the fresh variable
/// underneath.
///
/// Descending `Not` here grants NO authority: the pairs it records are still
/// vetted by the minted-definition lane's own FRESH / SORT / SINGLE-DEFINIENS /
/// INDEPENDENT tests, and the checker re-decides all four over the finished
/// proof.
pub(super) fn align_through_not(
    terms: &ay_core::TermStore,
    leaf: TermId,
    root: TermId,
    out: &mut Vec<(TermId, TermId)>,
    budget: &mut usize,
) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    if leaf == root {
        return true;
    }
    match (terms.get(leaf), terms.get(root)) {
        (TermData::App(left_sym, left_args), TermData::App(right_sym, right_args))
            if left_sym == right_sym && left_args.len() == right_args.len() =>
        {
            let pairs: Vec<(TermId, TermId)> = left_args
                .iter()
                .copied()
                .zip(right_args.iter().copied())
                .collect();
            for (left, right) in pairs {
                if !align_through_not(terms, left, right, out, budget) {
                    return false;
                }
            }
            true
        }
        (TermData::Not(left_inner), TermData::Not(right_inner)) => {
            let (left, right) = (*left_inner, *right_inner);
            align_through_not(terms, left, right, out, budget)
        }
        _ => {
            out.push((leaf, root));
            true
        }
    }
}

impl Executor {
    /// Replace every premiseless `trust` step whose unit clause is an `and`
    /// application that the whole-term congruence route cannot explain, by
    /// deriving it CONJUNCT BY CONJUNCT. Returns the number of leaves replaced.
    pub(in crate::executor) fn derive_conjunctwise_decomposed_leaves(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> usize {
        // Guard 1.
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return 0;
        }
        let leaves: Vec<(usize, TermId)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                is_decomposition_candidate(&self.ctx.terms, step).map(|atom| (index, atom))
            })
            .take(MAX_DECOMPOSED_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_DECOMPOSED_LEAVES {
            return 0;
        }
        // Guard 3: the roots this lane may `assume`, and the base pool, are the
        // sibling lanes' exactly.
        let roots = self.nonequality_roots(problem_assertions);
        if roots.is_empty() {
            return 0;
        }
        let (base_pool, base_leaf_of) = self.bridge_hypothesis_pool(proof, problem_assertions);
        let constrained = self.minted_constrained_names(proof, problem_assertions);
        let existing = self.existing_fresh_definitions(proof);
        let overrides = self.last_proof_term_overrides.clone();
        let context = MintContext {
            roots: &roots,
            base_pool: &base_pool,
            base_leaf_of: &base_leaf_of,
            constrained: &constrained,
            existing: &existing,
            overrides: overrides.as_ref(),
        };

        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (step, atom) in leaves {
            let Some(fragment) = self.plan_decomposed_fragment(atom, &context) else {
                continue;
            };
            plans[step] = Some(fragment);
            planned += 1;
        }
        if planned == 0 {
            return 0;
        }
        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let derived = self.commit_bridge_fragments(proof, plans);
        if derived == 0 {
            return 0;
        }
        // GATE 2 — the checker's OWN whole-proof fresh-definition validation,
        // against the UNION of both authored scopes. A superset scope can only
        // make the freshness test stricter, never more permissive.
        let mut scope: Vec<TermId> = problem_assertions.to_vec();
        let seen: DetHashSet<TermId> = scope.iter().copied().collect();
        for assertion in self.complete_problem_assertions_for_strict_proof() {
            if !seen.contains(&assertion) {
                scope.push(assertion);
            }
        }
        if ay_proof::FreshDefRegistry::collect(proof, &self.ctx.terms, Some(&scope)).is_err() {
            proof.steps = original;
            proof.named_steps = original_named;
            return 0;
        }
        derived
    }

    /// Plan the replacement fragment for one leaf, or `None`.
    fn plan_decomposed_fragment(
        &mut self,
        atom: TermId,
        context: &MintContext<'_>,
    ) -> Option<Vec<ProofStep>> {
        let conjuncts: Vec<TermId> = conjunction_children(&self.ctx.terms, atom)?.to_vec();
        if conjuncts.len() < 2 || conjuncts.len() > MAX_DECOMPOSED_CONJUNCTS {
            return None;
        }
        let key = ("and".to_string(), conjuncts.len());
        let candidates = context.roots.get(&key)?.clone();
        for root in candidates.into_iter().take(MAX_DECOMPOSED_ROOTS_PER_LEAF) {
            if root == atom {
                continue;
            }
            // Guard 3, second half: the root is an `and` of the SAME arity.
            let Some(root_conjuncts) = conjunction_children(&self.ctx.terms, root) else {
                continue;
            };
            if root_conjuncts.len() != conjuncts.len() {
                continue;
            }
            let root_conjuncts: Vec<TermId> = root_conjuncts.to_vec();
            // Guard 5: the definitions, minted once for the WHOLE leaf so the
            // single-definiens decision is taken across every conjunct.
            let Some(minted) = self.mint_decomposition_definitions(atom, root, context) else {
                continue;
            };
            let Some(fragment) = self.assemble_decomposition(
                atom,
                root,
                &conjuncts,
                &root_conjuncts,
                &minted,
                context,
            ) else {
                continue;
            };
            // Guard 9.
            if self.bridge_fragment_is_unrenderable(&fragment, atom, context.overrides) {
                continue;
            }
            return Some(fragment);
        }
        None
    }

    /// Guard 5: the `fresh_def_eq` definitions this leaf needs, minted under
    /// the minted-definition lane's OWN vetting.
    fn mint_decomposition_definitions(
        &mut self,
        atom: TermId,
        root: TermId,
        context: &MintContext<'_>,
    ) -> Option<Vec<Minted>> {
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        let mut budget = MAX_ALIGN_NODES;
        if !align_through_not(&self.ctx.terms, atom, root, &mut pairs, &mut budget) {
            return None;
        }
        if pairs.is_empty() || pairs.len() > MAX_MINTED_PER_LEAF {
            return None;
        }
        self.mint_definitions_from_pairs(&pairs, context.constrained, context.existing)
    }
}

#[cfg(test)]
#[path = "conjunct_decomposition_leaf_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "conjunct_decomposition_leaf_guard_tests.rs"]
mod guard_tests;

#[cfg(test)]
#[path = "conjunct_decomposition_leaf_negative_tests.rs"]
mod negative_tests;
