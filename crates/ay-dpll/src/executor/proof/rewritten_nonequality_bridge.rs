// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derive a REWRITTEN authored assertion whose goal is **not** a binary `=`.
//!
//! # The class, as measured
//!
//! `rewritten_assertion_bridge` closes the rewritten assertions whose clause is
//! a unit binary `=`, because `ay_proof::plan_definitional_bridge` reads its
//! goal as the single POSITIVE literal of a congruence-explanation clause and
//! that literal must be an equality. Preprocessing rewrites every OTHER
//! assertion shape too, and the demoted leaf then carries a `<=`, a `not`, an
//! `and`, a `mem`, a `str.is_digit`, … — none of which that lane can take as a
//! goal. Measured over all 639 `.smt2` under `benchmarks/`
//! (`ay solve --no-proof -T:10`, one process per file), the leaves whose unit
//! clause is a rewrite of an AUTHORED assertion under the problem's own
//! definitions, by an INDEPENDENT re-parse of the dumped clauses:
//!
//! | steps | shape | files |
//! |---|---|---|
//! | 20 | `<=#2` | `QF_LIA/ring_2exp16_5vars_cascade_unsat` |
//! | 5 | `not[=#2]` | 4 QF_AUFLIA / QF_ALIA |
//! | 2 | `not[mem#2]` | 2 `soundness_qf_uf_incremental` |
//! | 1 each | `and#N`, `str.is_digit#1`, `seq.suffixof#2` | 3 |
//!
//! The head of it is the `VariableSubstitution` shape the sibling lane already
//! serves, with a non-equality assertion on the outside:
//!
//! ```text
//! authored   (assert (= x1 (* m1 3)))
//! authored   (assert (<= 0 x1))
//! asserted   (<= 0 (* m1 3))
//! ```
//!
//! # What replaces the leaf
//!
//! The bridge is the sibling lane's, run on the EQUALITY BETWEEN the authored
//! assertion and the leaf, plus the one propositional step that turns that
//! equality into the leaf:
//!
//! ```text
//!  i+0 .. i+k-1   one leaf per cited hypothesis        (the sibling's pool)
//!  i+k .. i+m     the congruence derivation            (cl ¬h_1 .. ¬h_k (= A G))
//!  i+m+1 .. i+n   th_resolution, one per hypothesis    (cl (= A G))
//!  i+n+1          assume A                             an EXACT member of both scopes
//!  i+n+2          equiv_pos1 / equiv_pos2              (cl ¬(= A G) ¬A G)
//!  i+n+3          th_resolution                        (cl ¬A G)
//!  i+n+4          th_resolution                        (cl G)
//! ```
//!
//! `equiv_pos1` and `equiv_pos2` are in [`ay_core::CHECKABLE_ALETHE_RULES`]
//! with strict validators in `ay-proof` (`validate_equiv_pos1` /
//! `validate_equiv_pos2`). NOTHING in the checker is touched by this lane.
//!
//! # Authority
//!
//! The only term this lane assumes is `A`, an authored assertion in the
//! INTERSECTION of the scope the rewrite was handed and the scope the strict
//! presentation checks against — exactly the sibling lane's Guard 3. Every
//! other step is a premise-free tautology the checker decides from the clause
//! alone, or a resolution decided from its premises. Both the congruence
//! derivation AND the propositional step are closed into self-contained
//! refutations and replayed by the UNTOUCHED `check_proof_strict` before
//! anything may be committed; the whole rebuilt proof is then re-checked and
//! reverted wholesale if it does not check or if it costs a certification the
//! original had. A declined leaf keeps its byte-identical `trust` step.
//!
//! # Guards
//!
//! Each is mutation-checked in `rewritten_nonequality_bridge_tests.rs`.
//!
//! 1. **No anchors** — their forward references the in-order remap cannot
//!    resolve.
//! 2. **A premiseless, argument-free `trust` step with a unit clause that is
//!    NOT a binary `=`.** The equality goals belong to the sibling lane and
//!    this one never competes for them, so the two populations are disjoint by
//!    construction.
//! 3. **The assumed root is in BOTH authored scopes** — the sibling's pool
//!    rule, reused verbatim.
//! 4. **The fragment ends on exactly the leaf's clause**, byte for byte.
//! 5. **The fragment RENDERS** under the export's own surface overrides.
//! 6. **The congruence derivation strict-checks** on its own.
//! 7. **The propositional step strict-checks** on its own, closed — which is
//!    also how the lane CHOOSES between `equiv_pos1` and `equiv_pos2` rather
//!    than re-deriving the checker's operand-order convention here.
//! 8. **`(= A G)` is a binary `=` APPLICATION over exactly `A` and `G`.**
//!    `mk_eq` folds a Boolean equality in six different ways (`(= x true)` is
//!    `x`, `(= (not x) (not y))` is `(= x y)`, …), so the built term is decoded
//!    back and the lane declines whenever it is not the node the bridge needs.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermData, TermId};

use super::super::Executor;
use super::rewritten_assertion_bridge::{is_binary_equality, HypothesisLeaf};

/// Largest number of `trust` leaves one call will plan for. Mirrors the
/// sibling lane's cap; the measured per-proof population is 1-20.
const MAX_NONEQ_LEAVES: usize = 512;

/// Largest number of AUTHORED roots one leaf will be tried against. Each try
/// runs a congruence closure over the whole hypothesis pool, so this bounds
/// the per-leaf cost on an adversarial problem. The measured population needs
/// 1-5.
const MAX_ROOTS_PER_LEAF: usize = 64;

/// Whether `step` is a leaf this lane may replace (Guard 2).
fn is_nonequality_candidate(terms: &ay_core::TermStore, step: &ProofStep) -> Option<TermId> {
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
    // The binary-`=` goals are the SIBLING lane's population, and this lane
    // never competes for one.
    (!is_binary_equality(terms, atom)).then_some(atom)
}

/// The head symbol and arity of a term, for the cheap root pre-filter.
pub(super) fn head_key(terms: &ay_core::TermStore, term: TermId) -> Option<(String, usize)> {
    match terms.get(term) {
        TermData::App(ay_core::Symbol::Named(name), args) => Some((name.clone(), args.len())),
        TermData::Not(_) => Some(("not".to_string(), 1)),
        _ => None,
    }
}

impl Executor {
    /// Replace every premiseless `trust` step whose unit clause is a
    /// congruence-derivable rewrite of an AUTHORED assertion and is NOT a
    /// binary `=`. Returns the number of leaves replaced.
    pub(in crate::executor) fn derive_rewritten_nonequality_assertions(
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
                is_nonequality_candidate(&self.ctx.terms, step).map(|atom| (index, atom))
            })
            .take(MAX_NONEQ_LEAVES.saturating_add(1))
            .collect();
        if leaves.is_empty() || leaves.len() > MAX_NONEQ_LEAVES {
            return 0;
        }
        let (pool, leaf_of) = self.bridge_hypothesis_pool(proof, problem_assertions);
        if pool.is_empty() {
            return 0;
        }
        // Guard 3: the roots this lane may `assume` are exactly the sibling
        // lane's authored half — the INTERSECTION of both scopes — with the
        // binary-`=` restriction dropped, because the root here is the
        // assertion being rewritten rather than a cited hypothesis.
        let roots = self.nonequality_roots(problem_assertions);
        if roots.is_empty() {
            return 0;
        }
        let overrides = self.last_proof_term_overrides.clone();
        let mut plans: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut planned = 0usize;
        for (index, atom) in leaves {
            let Some(fragment) = self.plan_nonequality_fragment(atom, &pool, &leaf_of, &roots)
            else {
                continue;
            };
            // Guard 5.
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

    /// The AUTHORED assertions this lane may `assume`, grouped so a leaf only
    /// sees the roots whose head and arity could possibly be congruent to it.
    pub(super) fn nonequality_roots(
        &self,
        problem_assertions: &[TermId],
    ) -> DetHashMap<(String, usize), Vec<TermId>> {
        let strict_scope: ay_core::kani_compat::DetHashSet<TermId> = self
            .complete_problem_assertions_for_strict_proof()
            .into_iter()
            .collect();
        let mut roots: DetHashMap<(String, usize), Vec<TermId>> = DetHashMap::default();
        for &assertion in problem_assertions {
            if !strict_scope.contains(&assertion) {
                continue;
            }
            let Some(key) = head_key(&self.ctx.terms, assertion) else {
                continue;
            };
            let entry = roots.entry(key).or_default();
            if !entry.contains(&assertion) {
                entry.push(assertion);
            }
        }
        roots
    }

    /// Plan the replacement fragment for one leaf, or `None`.
    pub(super) fn plan_nonequality_fragment(
        &mut self,
        atom: TermId,
        pool: &[TermId],
        leaf_of: &DetHashMap<TermId, HypothesisLeaf>,
        roots: &DetHashMap<(String, usize), Vec<TermId>>,
    ) -> Option<Vec<ProofStep>> {
        let key = head_key(&self.ctx.terms, atom)?;
        let candidates = roots.get(&key)?;
        for &root in candidates.iter().take(MAX_ROOTS_PER_LEAF) {
            if root == atom {
                continue;
            }
            if self.ctx.terms.sort(root) != self.ctx.terms.sort(atom) {
                continue;
            }
            // Guard 8: a binary `=` APPLICATION, or nothing. `mk_eq` folds a
            // Boolean equality in six different ways — `(= x true)` is `x`,
            // two constants are `false`, `(= (not x) (not y))` LIFTS to
            // `(= x y)` — so the built term is decoded back and anything that
            // is not the node the bridge reads as its goal is declined. The
            // lifted form is KEPT: `(= x y)` is exactly the equality that
            // licenses `(not x) -> (not y)`, and Guard 7 below re-derives
            // whether the propositional step over it is a tautology at all.
            let goal = self.ctx.terms.mk_eq(root, atom);
            if !is_binary_equality(&self.ctx.terms, goal) {
                continue;
            }
            let Some(bridge) = ay_proof::plan_definitional_bridge(&mut self.ctx.terms, goal, pool)
            else {
                continue;
            };
            // Guard 6.
            let closed =
                ay_proof::close_congruence_derivation(&mut self.ctx.terms, &bridge.derivation);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
                continue;
            }
            let Some(mut fragment) = self.assemble_bridge_fragment(&bridge, leaf_of, goal) else {
                continue;
            };
            let Some(equality_step) = fragment.len().checked_sub(1) else {
                continue;
            };
            let Some(rule) = self.equivalence_rule_for(goal, root, atom) else {
                continue;
            };
            let not_goal = self.ctx.terms.mk_not(goal);
            let complement = self.ctx.terms.mk_not(root);
            fragment.push(ProofStep::Assume(root));
            let assumed = fragment.len() - 1;
            fragment.push(ProofStep::Step {
                rule,
                clause: vec![not_goal, complement, atom],
                premises: Vec::new(),
                args: Vec::new(),
            });
            let tautology = fragment.len() - 1;
            fragment.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![complement, atom],
                premises: vec![
                    ProofId(u32::try_from(tautology).ok()?),
                    ProofId(u32::try_from(equality_step).ok()?),
                ],
                args: Vec::new(),
            });
            let resolved = fragment.len() - 1;
            fragment.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![atom],
                premises: vec![
                    ProofId(u32::try_from(resolved).ok()?),
                    ProofId(u32::try_from(assumed).ok()?),
                ],
                args: Vec::new(),
            });
            // Guard 4.
            match fragment.last() {
                Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [atom] => {}
                _ => continue,
            }
            return Some(fragment);
        }
        None
    }

    /// Which `equiv_pos` rule states `(cl ¬(= A G) ¬A G)` for THIS operand
    /// order — decided by CLOSING the one-step fragment and asking the
    /// untouched strict checker, not by re-deriving the checker's convention
    /// (Guard 7).
    fn equivalence_rule_for(
        &mut self,
        goal: TermId,
        root: TermId,
        atom: TermId,
    ) -> Option<AletheRule> {
        let not_goal = self.ctx.terms.mk_not(goal);
        // The gate literal must be a plain `Not` wrapper: `mk_not` normalises
        // De Morgan, and a literal that is not the wrapper is not what the
        // validator reads as `(not (= ..))`.
        if !matches!(self.ctx.terms.get(not_goal), TermData::Not(inner) if *inner == goal) {
            return None;
        }
        let complement = self.ctx.terms.mk_not(root);
        let clause = vec![not_goal, complement, atom];
        for rule in [AletheRule::EquivPos1, AletheRule::EquivPos2] {
            let derivation = ay_proof::CongruenceDerivation {
                steps: vec![ProofStep::Step {
                    rule: rule.clone(),
                    clause: clause.clone(),
                    premises: Vec::new(),
                    args: Vec::new(),
                }],
                clause: clause.clone(),
            };
            let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_ok() {
                return Some(rule);
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "rewritten_nonequality_bridge_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "rewritten_nonequality_bridge_negative_tests.rs"]
mod negative_tests;
