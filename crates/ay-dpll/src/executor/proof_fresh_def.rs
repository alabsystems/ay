// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Promote a demoted definitional bound or EQUALITY to a CHECKED
//! fresh-definition step.
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
//! `purify_bool_args` does the same thing in the more DIRECT form: for a
//! COMPOUND Boolean argument `b` of an uninterpreted `f`, it mints a fresh
//! Boolean `p` and asserts `(= p b)` so that EUF can congruence-close over
//! `f(p)`. That assertion demotes to the same premiseless `trust`, and this
//! lane promotes it to [`AletheRule::FreshDefEq`].
//!
//! # What this class is NOT — measured, on the whole corpus
//!
//! Measured over all 639 `.smt2` under `benchmarks/`, `ay solve --no-proof
//! -T:10`: `(= d expr)` premiseless `trust` units are **236 steps in 43
//! files**, and a definitional equality over a FRESH symbol is **8 of those
//! 236 (3.4%), in 4 files**. The rest are not definitions at all and this lane
//! correctly declines them, classified by the FIRST guard each one fails:
//!
//! | steps | share | what they are |
//! |---|---|---|
//! | 161 | 68.2% | every atomic-variable side occurs in the AUTHORED problem — REWRITTEN/propagated assertions, and congruence-derived equalities between authored symbols |
//! | 67 | 28.4% | neither side is an atomic variable (`(= (select ..) (select ..))`, `(= (* q 2) (* r 3))`, store-chain equalities) |
//! | 8 | 3.4% | genuine fresh definitional equalities — every one from `purify_bool_args` |
//!
//! Do NOT read the `=#2` census class as "definitions". It is dominated by the
//! same REWRITTEN-assertion population the bound form's residual already named.
//! The freshness verdict was corroborated independently of this code: 162 of
//! the 163 distinct (file, symbol) pairs the traversal calls constrained are
//! present verbatim in the benchmark's own `.smt2` text, and the one exception
//! is a CHC sub-query variable the clause instance genuinely constrains.
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
//! binary `<=` or `=` with at least one atomic-variable operand at the same
//! sort as the other. A `<=` candidate has exactly one ORIENTATION (the `<=`
//! form is not symmetric and the producer requires exactly one variable side);
//! an `=` candidate over two variables has two, and the orientation is chosen
//! in stage A below.
//!
//! **Stage A — ELIGIBILITY.** A name `n` is eligible when
//!
//!  1. `n` occurs in no problem assertion (the authored scope, unioned across
//!     both gates that will re-check it), and
//!  2. `n` occurs in no `assume` step of the proof.
//!
//! Each candidate keeps the FIRST orientation whose definiendum name is
//! eligible, and is dropped outright when it has none. Stage A depends only on
//! the problem and the proof's assumes, so it is decided once and never
//! revisited.
//!
//! **Stage B — INDEPENDENCE and UNIQUENESS**, over the ELIGIBLE candidates
//! only. A surviving candidate is promoted when
//!
//!  3. its name occurs in NO eligible candidate's defining term — which also
//!     covers `n` occurring in its own, and every longer
//!     `d1 := f(d2), d2 := g(d1)` cycle; and
//!  4. every eligible candidate naming `n` carries the SAME defining term
//!     (across BOTH rules: an equality and a bound by different terms are two
//!     definitions of one symbol, and jointly they constrain the problem's own
//!     variables).
//!
//! (3) is what removes the need to iterate: the promoted set is a subset of the
//! eligible set, so a name absent from every ELIGIBLE definiens is absent from
//! every PROMOTED one, which is exactly the checker's condition. One pass is a
//! fixpoint.
//!
//! Scoping (3) to the ELIGIBLE candidates rather than to ALL of them is what
//! makes the measured `purify_bool_args` population reachable: the rewritten
//! assertion `(= TRUE (bool p))` is a candidate whose definiendum `TRUE` is
//! AUTHORED, so it can never be promoted — and counting its definiens would
//! block `p`'s own, genuine, definition for no soundness reason. Measured on
//! the corpus: **6** of the 8 fresh Boolean proxies are promotable under the
//! ALL-candidates reading, **8 of 8** under this one, with 0 verdict flips
//! either way.
//!
//! A final belt-and-braces gate runs the checker's own
//! `FreshDefRegistry::collect` over the rewritten proof and reverts the WHOLE
//! rewrite if it declines, so producer and checker cannot drift apart.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
#[cfg(test)]
use ay_core::AletheRule;
use ay_core::{Proof, ProofStep, TermId};

use super::Executor;

#[path = "proof_fresh_def_candidates.rs"]
mod candidates;
use candidates::{Candidate, DefKind, Orientation};

/// A candidate that survived stage A, with its chosen reading.
struct Eligible<'a> {
    step: usize,
    kind: DefKind,
    orientation: &'a Orientation,
}

impl Executor {
    /// Replace every premiseless `trust` step that is a definitional bound or
    /// EQUALITY over a genuinely fresh symbol with a checked
    /// `fresh_def_bound` / `fresh_def_eq` step.
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
            .map(|&(index, _, _)| (index, proof.steps[index].clone()))
            .collect();
        for &(index, definiendum, kind) in &rewrites {
            let ProofStep::Step { clause, .. } = &proof.steps[index] else {
                continue;
            };
            let atom = clause.clone();
            proof.steps[index] = ProofStep::Step {
                rule: kind.rule(),
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
    /// Returns `(step index, definiendum, kind)` for each promotable candidate.
    fn select_promotable_bounds(
        &self,
        proof: &Proof,
        problem_assertions: &[TermId],
        candidates: &[Candidate],
    ) -> Vec<(usize, TermId, DefKind)> {
        // STAGE A, conditions (1) + (2), in one shared traversal. Both authored
        // scopes are unioned in: the strict presentation gate and the
        // deferred-trust discharge gate assemble their premise sets slightly
        // differently, and a name either of them considers constrained must not
        // be promoted.
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

        // Each candidate keeps its FIRST eligible reading, or is dropped. The
        // choice is deterministic (collection order), so two runs over the same
        // proof promote the same steps.
        let eligible: Vec<Eligible<'_>> = candidates
            .iter()
            .filter_map(|candidate| {
                candidate
                    .orientations
                    .iter()
                    .find(|orientation| !constrained.contains(&orientation.name))
                    .map(|orientation| Eligible {
                        step: candidate.step,
                        kind: candidate.kind,
                        orientation,
                    })
            })
            .collect();
        if eligible.is_empty() {
            return Vec::new();
        }

        // STAGE B (4): one definiens per name, and one definiendum `TermId` per
        // name -- across BOTH kinds, because a symbol bounded by one term and
        // equated to another has two definitions.
        let mut definiens_of: HashMap<&str, (TermId, TermId)> = HashMap::default();
        let mut conflicted: HashSet<&str> = HashSet::default();
        for entry in &eligible {
            let orientation = entry.orientation;
            match definiens_of.get(orientation.name.as_str()) {
                Some(&(definiendum, definiens)) => {
                    if definiendum != orientation.definiendum || definiens != orientation.definiens
                    {
                        conflicted.insert(orientation.name.as_str());
                    }
                }
                None => {
                    definiens_of.insert(
                        orientation.name.as_str(),
                        (orientation.definiendum, orientation.definiens),
                    );
                }
            }
        }

        // STAGE B (3): no eligible name inside any ELIGIBLE defining term.
        let mut definiens_names: HashSet<String> = HashSet::default();
        let mut definiens_visited: HashSet<TermId> = HashSet::default();
        for entry in &eligible {
            self.collect_proof_symbol_names(
                entry.orientation.definiens,
                &mut definiens_names,
                &mut definiens_visited,
            );
        }

        eligible
            .iter()
            .filter(|entry| {
                !conflicted.contains(entry.orientation.name.as_str())
                    && !definiens_names.contains(&entry.orientation.name)
            })
            .map(|entry| (entry.step, entry.orientation.definiendum, entry.kind))
            .collect()
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

/// Whether `step` is a well-formed `fresh_def_eq` step. Same discipline as the
/// bound shim above: the tests read the finished proof through the checker's
/// own recognizer, never through this lane's private helpers.
#[cfg(test)]
pub(in crate::executor) fn is_fresh_def_eq_step(
    terms: &ay_core::TermStore,
    step: &ProofStep,
) -> bool {
    use ay_core::proof_validation::recognize_fresh_def_eq;
    let ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause,
        premises,
        args,
    } = step
    else {
        return false;
    };
    recognize_fresh_def_eq(terms, clause, premises.len(), args).is_ok()
}

#[cfg(test)]
#[path = "proof_fresh_def_tests.rs"]
mod tests;
