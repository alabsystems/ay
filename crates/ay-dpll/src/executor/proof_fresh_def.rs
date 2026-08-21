// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Promote a demoted definitional bound to a CHECKED fresh-definition step.
//!
//! # The class this closes
//!
//! The `EqDiffVar` preprocessing pass (`preprocess/eq_diffvar`) mints a symbol
//! `d` the problem never mentions and asserts the pair `(<= d lin)` /
//! `(>= d lin)` — canonically `(<= d lin)` and `(<= lin d)` — so that
//! multi-variable equality atoms fold to var-CONST atoms over `d`. Those two
//! assertions are solver-invented, so they are (correctly) not on the
//! `proof_exportable_assertions` whitelist, and `demote_non_problem_assumptions`
//! turns each into a premiseless `trust` step that strict certification then
//! rejects — throwing away a CORRECT refutation. On `dillig12_m` this is the
//! largest trust-kind class by a wide margin.
//!
//! # Why this lane is not "widening what counts as authored"
//!
//! It never claims the bound was authored. It replaces the unverified `trust`
//! with [`AletheRule::FreshDefBound`], a step the UNTOUCHED strict checker
//! re-validates from scratch through `ay_proof`'s `FreshDefRegistry` — which
//! decides freshness by traversing the PROBLEM's own terms rather than trusting
//! a name prefix or this lane's say-so. The soundness argument (any model of
//! the assumes extends to one satisfying the bound, by `d := lin`) lives with
//! that registry; see its module docs.
//!
//! # Ordering: this runs AFTER demotion, on `trust` steps
//!
//! Deliberately, and it is load-bearing. Freshness is a statement about the
//! finished proof's `assume` set, which is what the checker will test against.
//! Before demotion the preprocessed assertions that MENTION `d` (the folded
//! `(or g (= d 0))` bodies) are still `Assume` steps, so `d` would look
//! constrained and every conversion would decline; after demotion they are
//! `trust` steps, which are not premises of anything (strict rejects them, and
//! the deferred lane discharges each one independently against the authored
//! problem). Running here therefore makes this lane's admission test agree
//! EXACTLY with the checker's, which is what keeps a promotion from turning a
//! rescuable trust rejection into a hard `InvalidTheoryLemma` one.
//!
//! # The admission test, and why it needs no fixpoint
//!
//! Let `C` be the candidate `trust` steps: premiseless units whose clause is a
//! binary `<=` with EXACTLY one atomic-variable operand at the same sort as the
//! other. A candidate's variable name `n` is promotable when
//!
//!  1. `n` occurs in no problem assertion (the authored scope, unioned across
//!     both gates that will re-check it);
//!  2. `n` occurs in no `assume` step of the proof;
//!  3. `n` occurs in NO candidate's defining term — which also covers `n`
//!     occurring in its own, and every longer `d1 := f(d2), d2 := g(d1)` cycle;
//!  4. every candidate naming `n` carries the SAME defining term.
//!
//! (3) is what removes the need to iterate. A candidate that is NOT promoted
//! stays a `trust` step, and the only symbols such a step could contribute are
//! its own variable (some other `m ≠ n`) and its defining term — and (3)
//! already excluded `n` from every candidate defining term. So no decision here
//! can invalidate another, and one pass is a fixpoint.
//!
//! A final belt-and-braces gate runs the checker's own
//! `FreshDefRegistry::collect` over the rewritten proof and reverts the WHOLE
//! rewrite if it declines, so producer and checker cannot drift apart.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId};

use super::Executor;

/// Bound on how many bounds one proof may promote. Well past the pass's own
/// `MAX_DIFF_VARS` (1024) doubled, so it never binds in practice; it exists so
/// a pathological proof cannot make this lane's traversals unbounded.
const MAX_PROMOTED_BOUNDS: usize = 4096;

/// One promotable candidate.
struct Candidate {
    step: usize,
    definiendum: TermId,
    definiens: TermId,
    name: String,
}

impl Executor {
    /// Replace every premiseless `trust` step that is a definitional bound over
    /// a genuinely fresh symbol with a checked `fresh_def_bound` step.
    ///
    /// Declines silently, leaving today's `trust` step in place, whenever any
    /// admission condition fails. Nothing here can make a proof less
    /// certifiable than it already was.
    pub(in crate::executor) fn promote_fresh_definitional_bounds(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        let candidates = self.collect_fresh_def_candidates(proof);
        if candidates.is_empty() {
            return;
        }
        let rewrites = self.select_promotable_bounds(proof, problem_assertions, &candidates);
        if rewrites.is_empty() {
            return;
        }
        let restore: Vec<(usize, ProofStep)> = rewrites
            .iter()
            .map(|&(index, _)| (index, proof.steps[index].clone()))
            .collect();
        for &(index, definiendum) in &rewrites {
            let ProofStep::Step { clause, .. } = &proof.steps[index] else {
                continue;
            };
            let atom = clause.clone();
            proof.steps[index] = ProofStep::Step {
                rule: AletheRule::FreshDefBound,
                clause: atom,
                premises: Vec::new(),
                args: vec![definiendum],
            };
        }

        // Gate-2: the CHECKER's own whole-proof validation, run over the
        // rewritten proof exactly as the strict presentation will run it. A
        // decline reverts every promotion, so this lane can only ever leave the
        // proof as certifiable as it found it.
        if ay_proof::FreshDefRegistry::collect(proof, &self.ctx.terms, Some(problem_assertions))
            .is_err()
        {
            for (index, step) in restore {
                proof.steps[index] = step;
            }
        }
    }

    /// Decide which candidates satisfy conditions (1)-(4) of the module docs.
    ///
    /// Returns `(step index, definiendum)` for each promotable candidate.
    fn select_promotable_bounds(
        &self,
        proof: &Proof,
        problem_assertions: &[TermId],
        candidates: &[Candidate],
    ) -> Vec<(usize, TermId)> {
        // (4) one definiens per name, and one definiendum `TermId` per name.
        let mut definiens_of: HashMap<&str, (TermId, TermId)> = HashMap::default();
        let mut conflicted: HashSet<&str> = HashSet::default();
        for candidate in candidates {
            match definiens_of.get(candidate.name.as_str()) {
                Some(&(definiendum, definiens)) => {
                    if definiendum != candidate.definiendum || definiens != candidate.definiens {
                        conflicted.insert(candidate.name.as_str());
                    }
                }
                None => {
                    definiens_of.insert(
                        candidate.name.as_str(),
                        (candidate.definiendum, candidate.definiens),
                    );
                }
            }
        }

        // (1) + (2), in one shared traversal. Both authored scopes are unioned
        // in: the strict presentation gate and the deferred-trust discharge
        // gate assemble their premise sets slightly differently, and a name
        // either of them considers constrained must not be promoted.
        let mut constrained: HashSet<String> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        for &assertion in problem_assertions {
            self.collect_proof_symbol_names(assertion, &mut constrained, &mut visited);
        }
        for assertion in self.complete_problem_assertions_for_strict_proof() {
            self.collect_proof_symbol_names(assertion, &mut constrained, &mut visited);
        }
        for step in &proof.steps {
            if let ProofStep::Assume(term) = step {
                self.collect_proof_symbol_names(*term, &mut constrained, &mut visited);
            }
        }
        // (3) no candidate name inside ANY candidate's defining term.
        let mut definiens_names: HashSet<String> = HashSet::default();
        let mut definiens_visited: HashSet<TermId> = HashSet::default();
        for candidate in candidates {
            self.collect_proof_symbol_names(
                candidate.definiens,
                &mut definiens_names,
                &mut definiens_visited,
            );
        }

        candidates
            .iter()
            .filter(|candidate| {
                !conflicted.contains(candidate.name.as_str())
                    && !constrained.contains(&candidate.name)
                    && !definiens_names.contains(&candidate.name)
            })
            .map(|candidate| (candidate.step, candidate.definiendum))
            .collect()
    }

    /// Premiseless unit `trust` steps whose clause is a definitional bound.
    fn collect_fresh_def_candidates(&self, proof: &Proof) -> Vec<Candidate> {
        let mut candidates = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            if candidates.len() >= MAX_PROMOTED_BOUNDS {
                break;
            }
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            if !premises.is_empty() || !args.is_empty() {
                continue;
            }
            let [atom] = clause.as_slice() else {
                continue;
            };
            let Some((definiendum, definiens)) = self.fresh_def_bound_operands(*atom) else {
                continue;
            };
            let TermData::Var(name, _) = self.ctx.terms.get(definiendum) else {
                continue;
            };
            candidates.push(Candidate {
                step: index,
                definiendum,
                definiens,
                name: name.clone(),
            });
        }
        candidates
    }

    /// Split `(<= a b)` into `(definiendum, definiens)` when EXACTLY one side is
    /// an atomic variable at the other side's sort.
    ///
    /// Sort equality is checked here and again by the checker's recognizer: it
    /// is what guarantees `d := lin` is an assignment `d` can take at all. An
    /// `Int` symbol pinned between two `Real` bounds would instead force that
    /// term to be integral, which constrains the problem's own variables.
    fn fresh_def_bound_operands(&self, atom: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, operands) = self.ctx.terms.get(atom) else {
            return None;
        };
        if sym.name() != "<=" || operands.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (operands[0], operands[1]);
        let lhs_var = matches!(self.ctx.terms.get(lhs), TermData::Var(_, _));
        let rhs_var = matches!(self.ctx.terms.get(rhs), TermData::Var(_, _));
        let (definiendum, definiens) = match (lhs_var, rhs_var) {
            (true, false) => (lhs, rhs),
            (false, true) => (rhs, lhs),
            _ => return None,
        };
        (self.ctx.terms.sort(definiendum) == self.ctx.terms.sort(definiens))
            .then_some((definiendum, definiens))
    }

    /// Collect every symbol NAME reachable from `root`, sharing `visited`
    /// across roots so a whole assertion stack costs one DAG traversal.
    fn collect_proof_symbol_names(
        &self,
        root: TermId,
        names: &mut HashSet<String>,
        visited: &mut HashSet<TermId>,
    ) {
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !visited.insert(id) {
                continue;
            }
            match self.ctx.terms.get(id) {
                TermData::Var(name, _) => {
                    names.insert(name.clone());
                }
                TermData::App(sym, args) => {
                    names.insert(sym.name().to_string());
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (name, value) in bindings {
                        names.insert(name.clone());
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    for (name, _) in vars {
                        names.insert(name.clone());
                    }
                    stack.push(*body);
                    stack.extend(triggers.iter().flatten().copied());
                }
                _ => {}
            }
        }
    }
}

/// Whether `step` is a well-formed `fresh_def_bound` step. Test-facing shim so
/// the lane's own tests read the finished proof through the SAME recognizer the
/// checker uses.
#[cfg(test)]
pub(in crate::executor) fn is_fresh_def_bound_step(
    terms: &ay_core::TermStore,
    step: &ProofStep,
) -> bool {
    use ay_core::proof_validation::recognize_fresh_def_bound;
    let ProofStep::Step {
        rule: AletheRule::FreshDefBound,
        clause,
        premises,
        args,
    } = step
    else {
        return false;
    };
    recognize_fresh_def_bound(terms, clause, premises.len(), args).is_ok()
}

#[cfg(test)]
#[path = "proof_fresh_def_tests.rs"]
mod tests;
