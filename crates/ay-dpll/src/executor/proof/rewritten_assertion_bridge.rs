// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive a REWRITTEN assertion from the AUTHORED assertions and CHECKED
//! definitions it was rewritten from — the largest premiseless-`trust` class
//! whose clause is a unit `(= a b)`.
//!
//! # The class, as measured
//!
//! All 639 `.smt2` under `benchmarks/`, `ay solve --no-proof -T:10`, one
//! process per file: 222 premiseless, argument-free `trust` steps carry a unit
//! binary `=`, and **161 of them fail the fresh-definition guard because every
//! atomic-variable side occurs in the AUTHORED problem**. They are in **18
//! files**, and 142 of the 161 (88.2%) are the QF_AX `swap_*` family:
//!
//! | steps | share | shape |
//! |---|---|---|
//! | 118 | 73.3% | `(= e_N (select <inlined store chain> i))` |
//! | 24 | 14.9% | `(= e_A e_B)` — the same rewrite after a READ-OVER-WRITE fold |
//! | 11 | 6.8% | `(= a_N (store …))` |
//! | 8 | 5.0% | the rest: `(= x (select …))`, `(= TRUE (bool p))`, `(= t "cba")` |
//!
//! The producer is `VariableSubstitution`: it extracts an authored definition
//! `(= a_250 (store a1 i0 e_249))` and INLINES it into every other assertion,
//! so what the solver asserts is
//!
//! ```text
//! authored   (assert (= a_252 (store a_250 i1 e_251)))
//! authored   (assert (= e_253 (select a_252 i2)))
//! asserted   (= e_253 (select (store (store a1 i0 e_249) i1 e_251) i2))
//! ```
//!
//! The rewrite is not a problem assertion, so `demote_non_problem_assumptions`
//! turns it into a premiseless `trust` step. But it is ENTAILED by the
//! authored assertions, by CONGRUENCE alone.
//!
//! # What replaces the leaf
//!
//! ```text
//!  before                                     after
//!  i: (cl rewritten)  :rule trust             i+0 .. i+k-1  one leaf per cited hypothesis
//!                                             i+k .. i+m    the congruence derivation
//!                                             i+m+1 .. i+n  th_resolution, one per hypothesis
//!                                             i+n: (cl rewritten)
//! ```
//!
//! The LAST step's clause is byte-identical to the `trust` step's, so every
//! downstream premise reference, resolution and pivot sees exactly the clause
//! it saw before. No other step is added, removed or renumbered.
//!
//! A cited hypothesis is either
//!
//! * an AUTHORED assertion — cited by an `assume`, which the checker's own
//!   `validate_problem_assumptions` re-authorises against the problem scope;
//!   the pool is the INTERSECTION of the scope this rewrite was handed and the
//!   scope the strict presentation will check against, so a term either of
//!   them would refuse never enters a fragment; or
//! * a READ-OVER-WRITE axiom instance `(= (select (store a i v) i) v)` at a
//!   syntactically identical index, minted by
//!   `ay_proof::plan_row1_axiom_instances` and cited by a premise-free
//!   `ArraySelectStore { index_eq: true }` theory lemma; or
//! * a STORE-OVER-STORE axiom instance
//!   `(= (store (store B i u) i v) (store B i v))` at ONE index term, minted by
//!   `ay_proof::plan_store_overwrite_instances` and cited by a premise-free
//!   `ArrayRowChain` theory lemma (sub-schema (J)); or
//! * a CHECKED fresh definition — a premiseless `fresh_def_eq` step already in
//!   the proof, cited by an identical copy of that step. A copy rather than a
//!   premise reference because the definition may sit LATER in the proof than
//!   the leaf it explains (measured: on `hand_min_falsesat_bool_arg` the
//!   `trust` step is `t1` and its definition is `t4`), and a premise may only
//!   point backwards. `FreshDefRegistry` reads both copies, finds the same
//!   definiens for the same symbol, and accepts — the SINGLE DEFINIENS
//!   condition is about the definiens, not the step count.
//!
//! # Authority
//!
//! Nothing here is asserted. `ay_proof::plan_definitional_bridge` emits only
//! premise-free tautologies (`eq_congruent`, `eq_reflexive`, `eq_transitive`)
//! and steps decided from their premises (`th_resolution`, `weakening`,
//! `reordering`, `contraction`) — every one in `CHECKABLE_ALETHE_RULES` with a
//! strict validator in `ay-proof`. Before a plan may be committed the fragment
//! is CLOSED into a self-contained refutation and re-validated by the
//! untouched `check_proof_strict`; after the splice the whole proof is
//! re-checked and the rewrite is REVERTED if it costs a certification the
//! original had. A declined leaf keeps its byte-identical `trust` step.
//!
//! # Guards
//!
//! Each is mutation-checked in `rewritten_assertion_bridge_tests.rs`
//! (`GUARD_MUTATION_LEDGER` there).
//!
//! 1. **No anchors.** Their forward references the in-order remap cannot
//!    resolve — the same guard every sibling splice uses.
//! 2. **A premiseless, argument-free `trust` step with a unit clause.** A
//!    `trust` step WITH premises is a failed derivation, not a leaf, and
//!    relabelling it would drop the premises its consumer references.
//! 3. **The pool is the INTERSECTION of both authored scopes.** An `assume`
//!    of anything else is an unauthorised assumption the mandatory gate
//!    rejects outright — strictly worse than the `trust` step it replaces.
//! 4. **The fragment's last clause is byte-identical to the leaf's.**
//! 5. **The fragment RENDERS** under the export's own surface overrides.
//! 6. **The closed derivation strict-checks.**
//! 7. **Every ARRAY-AXIOM instance strict-checks on its own** before it may
//!    enter the pool — see `rewritten_assertion_bridge/array_axiom_pool.rs`
//!    and `ARRAY_GUARD_MUTATION_LEDGER` in
//!    `rewritten_assertion_bridge_array_tests.rs`.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermData, TermId};

use super::super::Executor;

/// Largest number of `trust` leaves one call will plan for. The measured
/// per-proof population is 1-30; the cap only bounds a pathological proof.
const MAX_BRIDGE_LEAVES: usize = 512;

/// Largest number of `and`-CONJUNCT entries the extended pool may carry. The
/// conjunct pool only exists to serve leaves the base pool already declines,
/// and this bounds the per-leaf second attempt on an adversarial input.
const MAX_CONJUNCT_POOL: usize = 512;

/// One `and_pos` descent: the parent conjunction, its RAW negation, the
/// argument position, and the child at that position.
#[derive(Clone)]
pub(super) struct ConjunctDescent {
    pub(super) position: u32,
    pub(super) parent: TermId,
    pub(super) not_parent: TermId,
    pub(super) child: TermId,
}

/// How a cited hypothesis is stated as a leaf inside the fragment.
#[derive(Clone)]
pub(super) enum HypothesisLeaf {
    /// An authored problem assertion: `assume`.
    Authored,
    /// A checked fresh definition already in the proof: an identical copy.
    Definition { rule: AletheRule, args: Vec<TermId> },
    /// A READ-OVER-WRITE axiom instance at an EQUAL index, minted by
    /// `ay_proof::plan_row1_axiom_instances` and accepted by the checker's own
    /// `recognize_array_select_store` before it may enter the pool: a
    /// premise-free `ArraySelectStore { index_eq: true }` theory lemma the
    /// strict gate re-validates from the clause alone.
    ArrayRowAxiom,
    /// A STORE-OVER-STORE axiom instance
    /// `(= (store (store B i u) i v) (store B i v))` at ONE index term, minted
    /// by `ay_proof::plan_store_overwrite_instances` and accepted by the
    /// checker's own `recognize_array_theory_lemma` before it may enter the
    /// pool: a premise-free `ArrayRowChain` theory lemma (sub-schema (J)) the
    /// strict gate re-validates from the clause alone.
    ArrayStoreOverwrite,
    /// An `and`-CONJUNCT of an authored problem assertion: `assume` of the
    /// ROOT (an exact member of both authored scopes), then one premiseless
    /// `and_pos` tautology plus a `th_resolution` per nesting level. The
    /// conjunct itself is never assumed — `validate_problem_assumptions`
    /// admits an `and`-conjunct assume but
    /// `validate_reachable_assumes_in_problem_scope` admits only EXACT
    /// membership, so an assumed conjunct is an authority the strict
    /// presentation would have to take on faith.
    Conjunct {
        root: TermId,
        descents: Vec<ConjunctDescent>,
    },
}

/// Whether `step` is a leaf this lane may replace.
fn is_bridge_candidate(terms: &ay_core::TermStore, step: &ProofStep) -> Option<TermId> {
    let ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises,
        args,
    } = step
    else {
        return None;
    };
    // Guard 2.
    if !premises.is_empty() || !args.is_empty() || clause.len() != 1 {
        return None;
    }
    let atom = clause[0];
    matches!(
        terms.get(atom),
        TermData::App(ay_core::Symbol::Named(name), operands)
            if name == "=" && operands.len() == 2
    )
    .then_some(atom)
}

/// Deepest `and` nesting the conjunct pool will descend.
const MAX_CONJUNCT_DEPTH: usize = 64;

/// The arguments of `term` when it is an `and` application.
fn conjunction_children(terms: &ay_core::TermStore, term: TermId) -> Option<Vec<TermId>> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) if name == "and" => Some(args.clone()),
        _ => None,
    }
}

/// Whether `term` is an `and` application.
fn is_conjunction(terms: &ay_core::TermStore, term: TermId) -> bool {
    conjunction_children(terms, term).is_some()
}

/// Whether `term` is a binary `=` application — the only pool shape a bridge
/// can cite.
pub(super) fn is_binary_equality(terms: &ay_core::TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(ay_core::Symbol::Named(name), operands)
            if name == "=" && operands.len() == 2
    )
}

impl Executor {
    /// Replace every premiseless `trust` step that carries a congruence-
    /// derivable rewritten assertion with a derivation of it. Returns the
    /// number of leaves replaced, which the tests assert on.
    pub(in crate::executor) fn derive_rewritten_assertions_by_congruence(
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
                is_bridge_candidate(&self.ctx.terms, step).map(|atom| (index, atom))
            })
            .take(MAX_BRIDGE_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_BRIDGE_LEAVES {
            return 0;
        }
        let (mut pool, mut leaf_of) = self.bridge_hypothesis_pool(proof, problem_assertions);
        // The ARRAY-AXIOM instances extend the BASE pool in place, so the
        // FIRST attempt below is byte-identical to the pool the array lane
        // already plans from. That lane never ran on an empty base pool —
        // it returned here — and the guard keeps that exact.
        if !pool.is_empty() {
            self.extend_pool_with_row1_axioms(&mut pool, &mut leaf_of, &leaves);
            // The STORE-OVER-STORE instances read the AUTHORED half of the
            // pool as their definition index, so they are planned from the
            // base pool before the read-over-write entries could be mistaken
            // for definitions: a minted axiom is never an authored equality.
            self.extend_pool_with_store_overwrite_axioms(&mut pool, &mut leaf_of, &leaves);
        }
        let overrides = self.last_proof_term_overrides.clone();
        // The CONJUNCT pool is a strict extension used only for leaves the
        // base pool declines outright, so every leaf the lane already derived
        // is planned from exactly the pool it was planned from before.
        let (conjunct_pool, conjunct_leaf_of) =
            self.bridge_conjunct_pool(problem_assertions, &pool);
        if pool.is_empty() && conjunct_pool.is_empty() {
            return 0;
        }
        let extended: Vec<TermId> = if conjunct_pool.is_empty() {
            Vec::new()
        } else {
            let mut extended = pool.clone();
            extended.extend_from_slice(&conjunct_pool);
            extended
        };
        leaf_of.extend(conjunct_leaf_of);
        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (index, atom) in leaves {
            let bridge = (!pool.is_empty())
                .then(|| ay_proof::plan_definitional_bridge(&mut self.ctx.terms, atom, &pool))
                .flatten()
                .or_else(|| {
                    (!extended.is_empty())
                        .then(|| {
                            ay_proof::plan_definitional_bridge(&mut self.ctx.terms, atom, &extended)
                        })
                        .flatten()
                });
            let Some(bridge) = bridge else {
                continue;
            };
            // Guard 6: the untouched strict checker replays every derivation
            // step before any of them may enter the proof.
            let closed =
                ay_proof::close_congruence_derivation(&mut self.ctx.terms, &bridge.derivation);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
                continue;
            }
            let Some(fragment) = self.assemble_bridge_fragment(&bridge, &leaf_of, atom) else {
                continue;
            };
            // Guard 5: the PRINTER decides renderability, with the export's
            // own overrides, so producer and exporter cannot drift.
            if self.bridge_fragment_is_unrenderable(&fragment, atom, overrides.as_ref()) {
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

    /// The hypotheses a bridge may cite, and how each one is stated.
    ///
    /// Guard 3: the authored half is the INTERSECTION of the scope this
    /// rewrite was handed and the scope the strict presentation checks
    /// against. A term only one of them admits would produce an `assume` the
    /// other refuses — a HARD `UnauthorizedAssumption`, strictly worse than
    /// the rescuable `trust` step this lane removes.
    pub(super) fn bridge_hypothesis_pool(
        &self,
        proof: &Proof,
        problem_assertions: &[TermId],
    ) -> (Vec<TermId>, DetHashMap<TermId, HypothesisLeaf>) {
        let strict_scope: DetHashSet<TermId> = self
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .collect();
        let mut pool: Vec<TermId> = Vec::new();
        let mut leaf_of: DetHashMap<TermId, HypothesisLeaf> = DetHashMap::default();
        for &assertion in problem_assertions {
            if !strict_scope.contains(&assertion) || !is_binary_equality(&self.ctx.terms, assertion)
            {
                continue;
            }
            if leaf_of
                .insert(assertion, HypothesisLeaf::Authored)
                .is_none()
            {
                pool.push(assertion);
            }
        }
        // CHECKED fresh definitions already in the proof. Only the premiseless
        // form: a definition with premises is a derivation whose premises a
        // copied leaf would not carry.
        for step in &proof.steps {
            let ProofStep::Step {
                rule: rule @ AletheRule::FreshDefEq,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            if !premises.is_empty() || clause.len() != 1 {
                continue;
            }
            let definition = clause[0];
            if !is_binary_equality(&self.ctx.terms, definition) {
                continue;
            }
            if leaf_of
                .insert(
                    definition,
                    HypothesisLeaf::Definition {
                        rule: rule.clone(),
                        args: args.clone(),
                    },
                )
                .is_none()
            {
                pool.push(definition);
            }
        }
        if pool.len() > ay_proof::MAX_BRIDGE_CANDIDATES {
            return (Vec::new(), DetHashMap::default());
        }
        (pool, leaf_of)
    }

    /// The `and`-CONJUNCT hypotheses, and the `and_pos` descent that DERIVES
    /// each one from an `assume` of its authored root.
    ///
    /// Guard 3 is preserved exactly: the only term ever assumed is the ROOT,
    /// and a root enters this pool only when it is in BOTH authored scopes —
    /// the scope this rewrite was handed and the scope the strict
    /// presentation checks against.
    fn bridge_conjunct_pool(
        &mut self,
        problem_assertions: &[TermId],
        base: &[TermId],
    ) -> (Vec<TermId>, DetHashMap<TermId, HypothesisLeaf>) {
        let strict_scope: DetHashSet<TermId> = self
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .collect();
        let mut pool: Vec<TermId> = Vec::new();
        let mut leaf_of: DetHashMap<TermId, HypothesisLeaf> = DetHashMap::default();
        let already: DetHashSet<TermId> = base.iter().copied().collect();
        for &root in problem_assertions {
            if !strict_scope.contains(&root) || !is_conjunction(&self.ctx.terms, root) {
                continue;
            }
            let mut stack: Vec<(TermId, Vec<ConjunctDescent>)> = vec![(root, Vec::new())];
            while let Some((node, descents)) = stack.pop() {
                if pool.len() >= MAX_CONJUNCT_POOL {
                    break;
                }
                let Some(children) = conjunction_children(&self.ctx.terms, node) else {
                    if descents.is_empty()
                        || already.contains(&node)
                        || leaf_of.contains_key(&node)
                        || !is_binary_equality(&self.ctx.terms, node)
                    {
                        continue;
                    }
                    leaf_of.insert(
                        node,
                        HypothesisLeaf::Conjunct {
                            root,
                            descents: descents.clone(),
                        },
                    );
                    pool.push(node);
                    continue;
                };
                // Bounded descent: an `and` tree deeper than this is not a
                // preprocessing shape, and the cap keeps the walk finite on
                // an adversarial input.
                if descents.len() >= MAX_CONJUNCT_DEPTH {
                    continue;
                }
                let not_parent = self.ctx.terms.mk_not_raw(node);
                for (position, child) in children.into_iter().enumerate() {
                    let Ok(position) = u32::try_from(position) else {
                        continue;
                    };
                    let mut next = descents.clone();
                    next.push(ConjunctDescent {
                        position,
                        parent: node,
                        not_parent,
                        child,
                    });
                    stack.push((child, next));
                }
            }
        }
        (pool, leaf_of)
    }
}

include!("rewritten_assertion_bridge/array_axiom_pool.rs");

#[cfg(test)]
#[path = "rewritten_assertion_bridge_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "rewritten_assertion_bridge_array_tests.rs"]
mod array_tests;

#[cfg(test)]
#[path = "rewritten_assertion_bridge_store_overwrite_tests.rs"]
mod store_overwrite_tests;
