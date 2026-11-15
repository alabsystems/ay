// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Promote the demoted atoms of a div/mod PURIFICATION to checked
//! `divmod_def` steps.
//!
//! # The class this closes
//!
//! `mod_div_elim` replaces `(div x k)` / `(mod x k)` for a non-zero literal `k`
//! by a fresh quotient `q` and remainder `r` and asserts their SMT-LIB
//! definition `x = k*q + r`, `0 <= r`, `r < |k|`. Those assertions are
//! solver-invented, so `demote_non_problem_assumptions` turns every one a
//! refutation uses into a premiseless `trust` step, and strict certification
//! refuses the whole proof (`step t0 uses unverified trust rule`) — even for
//! `(assert (< 100 (div x 2))) (assert (< x 10))`. The `fresh_def_bound` lane
//! can only read `(<= 0 r)` as the definition `r := 0`, and nothing reads the
//! equation at all.
//!
//! # What this lane does, and what it does not claim
//!
//! `mod_div_elim` records each pair's `(x, k)` at its single mint site
//! (`TermStore::register_divmod_purification`). For every pair whose quotient
//! or remainder a demoted atom mentions, this lane defines `q := (div x k)`
//! and `r := (mod x k)` from that record, and rewrites every premiseless unit
//! step whose atom is VALID under those two definitions into `divmod_def` with
//! `:args (q D r M)`:
//! the demoted `trust` atoms, and a `fresh_def_bound`/`fresh_def_eq` that gave
//! one of the two symbols another definiens (the bound lane's `r := 0`). A
//! rewritten authored leaf another lane read as a definition (`(= r 0)` from
//! `(= (mod x 4) 0)`) goes back to `trust` for the bridges to derive. It
//! never claims an atom was authored or is a tautology. The UNTOUCHED strict
//! checker re-decides validity (`recognize_divmod_def`) and the whole-proof
//! conditions (`FreshDefRegistry`: FRESH against the problem and every
//! `assume`, INDEPENDENT, SINGLE DEFINIENS across all three fresh-definition
//! rules).
//!
//! The mint-site record only CHOOSES candidates; it grants nothing (a stale or
//! wrong record could only cost the proof). A pair whose symbols the problem
//! or an `assume` mentions is declined here (stage A) exactly as the registry
//! would decline it.
//!
//! # Why it is the LAST pass of `build_unsat_proof`
//!
//! A `divmod_def` proof is strictly checked but cannot be rendered: no Alethe
//! document can declare the minted `q`/`r`. Several authored-root rebuilds key
//! on a `trust` step being present (`promote_lia_mod_range_collapse`, the
//! BV/LIA last resort, ...) and produce a proof over the authored roots alone,
//! which renders. Promoting earlier removed their trigger and replaced those
//! renderable documents by none (measured: `(= (mod x 3) 4)` lost its
//! `lia_mod_range` certificate). As the last pass, the lane only ever sees a
//! proof every other route left trust-bearing, and it commits only when the
//! result is strictly COMPLETE (after the derivation bridges of
//! `finish_input_syntax_rewrite` re-run with the new bindings to derive the
//! rewritten authored leaves); otherwise the proof is restored
//! byte-identically.
//!
//! # Gate 2
//!
//! After the rewrite the checker's own `FreshDefRegistry::collect` runs over
//! the whole proof; on any decline every promotion is reverted, so the lane
//! can never turn a rescuable `trust` rejection into a hard
//! `InvalidTheoryLemma` one.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::proof_validation::{
    recognize_divmod_def, recognize_fresh_def_bound, recognize_fresh_def_eq,
};
use ay_core::{AletheRule, Proof, ProofStep, TermId};

use crate::executor::Executor;

/// Bound on the pairs one proof may promote; it exists so a pathological proof
/// cannot make this lane's traversals unbounded.
const MAX_DIVMOD_PAIRS: usize = 4096;

/// The pairs that survive SINGLE DEFINIENS, and the existing definition steps
/// to reclaim as `divmod_def` or demote back to `trust`, by step index.
struct Resolved {
    pairs: Vec<Pair>,
    reclaimed: HashMap<usize, TermId>,
    demoted: HashMap<usize, TermId>,
}

/// One purification pair and the definitions it would receive.
struct Pair {
    quotient: TermId,
    quotient_definiens: TermId,
    remainder: TermId,
    remainder_definiens: TermId,
}

impl Pair {
    fn args(&self) -> Vec<TermId> {
        vec![
            self.quotient,
            self.quotient_definiens,
            self.remainder,
            self.remainder_definiens,
        ]
    }

    fn definiens_of(&self, symbol: TermId) -> Option<TermId> {
        if symbol == self.quotient {
            Some(self.quotient_definiens)
        } else if symbol == self.remainder {
            Some(self.remainder_definiens)
        } else {
            None
        }
    }
}

impl Executor {
    /// The last pass of `build_unsat_proof`: strictly derive the div/mod
    /// purification of a proof that is still trust-bearing, or leave the proof
    /// byte-identical.
    pub(in crate::executor) fn promote_divmod_definitions_last_resort(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.recover_divmod_pairs(proof).is_empty() {
            return;
        }
        // One stop for the pass (`make_proof_assembly_should_stop`).
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return;
        }
        let scope = self.complete_problem_assertions_for_strict_proof();
        let original = proof.clone();
        if !self.promote_divmod_purification_definitions(proof, &scope) {
            return;
        }
        // The rewritten authored leaves (`(< 100 q)`, `(= r 1)`, a negated
        // `(not (= r1 r2))`) are derived from their authored roots by the same
        // bridge family, in the same order, as `finish_input_syntax_rewrite`
        // runs it — now over the new definitions.
        let bridges: [fn(&mut Self, &mut Proof, &[TermId]) -> usize; 6] = [
            Self::derive_rewritten_assertions_by_congruence,
            Self::derive_rewritten_nonequality_assertions,
            Self::derive_authored_conjunct_leaves,
            Self::derive_leaves_over_minted_definitions,
            Self::derive_conjunctwise_decomposed_leaves,
            Self::derive_ite_definition_guard_leaves,
        ];
        for bridge in bridges {
            if stop() {
                break;
            }
            let _derived = bridge(self, proof, &scope);
        }
        let complete = !stop()
            && self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete());
        if !complete {
            *proof = original;
        }
    }

    /// Rewrite the atoms of every eligible div/mod purification pair into
    /// checked `divmod_def` steps. Returns whether anything was promoted;
    /// declines (leaving the proof untouched) whenever any admission condition
    /// fails.
    fn promote_divmod_purification_definitions(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> bool {
        let recovered = self.recover_divmod_pairs(proof);
        if recovered.is_empty() {
            return false;
        }
        let candidates = self.eligible_divmod_pairs(proof, problem_assertions, recovered);
        let Resolved {
            pairs,
            reclaimed,
            demoted,
        } = self.consistent_divmod_pairs(proof, candidates);
        if pairs.is_empty() {
            return false;
        }
        let mut owner: HashMap<TermId, usize> = HashMap::default();
        for (index, pair) in pairs.iter().enumerate() {
            owner.insert(pair.quotient, index);
            owner.insert(pair.remainder, index);
        }
        let mut restore: Vec<(usize, ProofStep)> = Vec::new();
        // A rewritten leaf another lane read as a definition goes back to the
        // `trust` it was: the congruence bridges derive it from its root.
        for (&index, &atom) in &demoted {
            let step = ProofStep::Step {
                rule: AletheRule::Trust,
                clause: vec![atom],
                premises: Vec::new(),
                args: Vec::new(),
            };
            restore.push((index, std::mem::replace(&mut proof.steps[index], step)));
        }
        let demoted_count = restore.len();
        for index in 0..proof.steps.len() {
            let Some(atom) = reclaimed
                .get(&index)
                .copied()
                .or_else(|| demoted_unit_atom(&proof.steps[index]))
            else {
                continue;
            };
            let Some(pair) = self.divmod_pair_of(atom, &owner).map(|i| &pairs[i]) else {
                continue;
            };
            let args = pair.args();
            if recognize_divmod_def(&self.ctx.terms, &[atom], 0, &args).is_err() {
                continue;
            }
            let step = ProofStep::Step {
                rule: AletheRule::DivModDef,
                clause: vec![atom],
                premises: Vec::new(),
                args,
            };
            restore.push((index, std::mem::replace(&mut proof.steps[index], step)));
        }
        if restore.len() == demoted_count {
            for (index, step) in restore {
                proof.steps[index] = step;
            }
            return false;
        }
        // Gate 2: the checker's own whole-proof validation.
        if ay_proof::FreshDefRegistry::collect(proof, &self.ctx.terms, Some(problem_assertions))
            .is_err()
        {
            for (index, step) in restore {
                proof.steps[index] = step;
            }
            return false;
        }
        // Intern `(= q D)` / `(= r M)` so the congruence bridges, which may
        // only LOOK terms up, can offer them as `fresh_def_eq` hypotheses.
        for (definiendum, definiens) in self.divmod_definition_bindings(proof) {
            let _interned = self.ctx.terms.mk_eq(definiendum, definiens);
        }
        true
    }

    /// SINGLE DEFINIENS against the definitions the proof already carries.
    ///
    /// A `fresh_def_bound`/`fresh_def_eq` naming a pair symbol either agrees
    /// with the pair's definiens (the minted `(= (div x 2) q)` bridge); or its
    /// atom is valid under the pair and it is RECLAIMED as a `divmod_def` (the
    /// bound lane's `(<= 0 r)` read as `r := 0`); or it is a rewritten authored
    /// leaf another lane read as a definition (`(= r 0)` from `(= (mod x 4)
    /// 0)`) and is DEMOTED back to `trust`, for the bridges to derive. Only a
    /// `divmod_def` with other definientia declines the pair.
    fn consistent_divmod_pairs(&self, proof: &Proof, candidates: Vec<Pair>) -> Resolved {
        let mut reclaimed: HashMap<usize, TermId> = HashMap::default();
        let mut demoted: HashMap<usize, TermId> = HashMap::default();
        let mut declined: HashSet<usize> = HashSet::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let Some((atom, bindings)) = self.fresh_definition_of(step) else {
                continue;
            };
            let is_divmod = matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::DivModDef,
                    ..
                }
            );
            for (definiendum, definiens) in bindings {
                let Some(pair_index) = candidates
                    .iter()
                    .position(|pair| pair.definiens_of(definiendum).is_some())
                else {
                    continue;
                };
                let pair = &candidates[pair_index];
                if pair.definiens_of(definiendum) == Some(definiens) {
                    continue;
                }
                if is_divmod {
                    declined.insert(pair_index);
                } else if recognize_divmod_def(&self.ctx.terms, &[atom], 0, &pair.args()).is_ok() {
                    reclaimed.insert(index, atom);
                } else {
                    demoted.insert(index, atom);
                }
            }
        }
        let pairs: Vec<Pair> = candidates
            .into_iter()
            .enumerate()
            .filter(|(index, _)| !declined.contains(index))
            .map(|(_, pair)| pair)
            .collect();
        let symbols: HashSet<TermId> = pairs
            .iter()
            .flat_map(|pair| [pair.quotient, pair.remainder])
            .collect();
        let survives = |index: &usize| {
            self.fresh_definition_of(&proof.steps[*index])
                .is_some_and(|(_, bindings)| bindings.iter().all(|(d, _)| symbols.contains(d)))
        };
        reclaimed.retain(|index, _| survives(index));
        demoted.retain(|index, _| survives(index));
        Resolved {
            pairs,
            reclaimed,
            demoted,
        }
    }

    /// The atom and `(definiendum, definiens)` bindings of a premiseless
    /// fresh-definition step, through the checker's own recognizers.
    fn fresh_definition_of(&self, step: &ProofStep) -> Option<(TermId, Vec<(TermId, TermId)>)> {
        let ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } = step
        else {
            return None;
        };
        let terms = &self.ctx.terms;
        let bindings = match rule {
            AletheRule::FreshDefEq => recognize_fresh_def_eq(terms, clause, premises.len(), args)
                .map(|shape| vec![(shape.definiendum, shape.definiens)])
                .ok(),
            AletheRule::FreshDefBound => {
                recognize_fresh_def_bound(terms, clause, premises.len(), args)
                    .map(|shape| vec![(shape.definiendum, shape.definiens)])
                    .ok()
            }
            AletheRule::DivModDef => recognize_divmod_def(terms, clause, premises.len(), args)
                .map(|shape| {
                    vec![
                        (shape.quotient, shape.quotient_definiens),
                        (shape.remainder, shape.remainder_definiens),
                    ]
                })
                .ok(),
            _ => None,
        }?;
        Some((*clause.first()?, bindings))
    }

    /// Every `(symbol, definiens)` binding the proof's `divmod_def` steps make,
    /// deduplicated, in proof order.
    pub(in crate::executor) fn divmod_definition_bindings(
        &self,
        proof: &Proof,
    ) -> Vec<(TermId, TermId)> {
        let mut bindings: Vec<(TermId, TermId)> = Vec::new();
        let mut seen: HashSet<(TermId, TermId)> = HashSet::default();
        for step in &proof.steps {
            let ProofStep::Step {
                rule: AletheRule::DivModDef,
                ..
            } = step
            else {
                continue;
            };
            let introduced = self.fresh_definition_of(step).map(|(_, b)| b);
            for binding in introduced.unwrap_or_default() {
                if seen.insert(binding) {
                    bindings.push(binding);
                }
            }
        }
        bindings
    }
}

/// The atom of a premiseless, argument-free unit `trust` step.
fn demoted_unit_atom(step: &ProofStep) -> Option<TermId> {
    match step {
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            args,
        } if premises.is_empty() && args.is_empty() && clause.len() == 1 => Some(clause[0]),
        _ => None,
    }
}

#[path = "proof_divmod_def_pairs.rs"]
mod pairs;

#[cfg(test)]
#[path = "proof_divmod_def_tests.rs"]
mod tests;
