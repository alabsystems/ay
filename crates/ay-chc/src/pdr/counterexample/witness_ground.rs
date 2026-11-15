// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! STEP D: the ground derivation a counterexample's derivation witness names.
//!
//! [`Counterexample::ground_checks_unsafe`] confirmed only two evidence
//! shapes: a carried [`GroundDerivation`], and the single-predicate transition
//! trace read off `steps`. A PDR counterexample carries neither in a form
//! that check could read. PDR attaches no ground derivation, and each of its
//! steps holds the query model of the clause that derived it, in that
//! clause's own variable names: a transition step names its PREDECESSOR's
//! values, so the trace form can pin at most time 0 and never ground-evaluates
//! the successor states. `build_cex` also listed the steps root first (the bad
//! state at step 0), so the trace form bound time 0 to the root's predecessor
//! value (`x = 5` for `inv(x) -> inv(x + 1)` deriving `inv(6)`), `init(0)`
//! evaluated to `false`, and a genuine counterexample was reported as
//! contradicting the transition relation. Which engine found the
//! counterexample is decided by wall-clock budgets (the front BMC probe's
//! soft budget), so the same UNSAFE script published `unsat` when BMC won and
//! was demoted to `unknown` when PDR won: under load, every time.
//!
//! The witness does name everything a ground derivation needs: per derived
//! fact, the clause that fired, its premises (positionally aligned with the
//! clause's body predicates), and concrete values of that clause's variables.
//! This module re-shapes it. It is VALUE SYNTHESIS, not a relaxed check:
//! [`crate::ground_derivation::validate_ground_derivation`] re-evaluates the
//! result in full against the caller's clauses and stays the sole acceptance
//! anchor, so a stale, transform-space or corrupted witness is rejected and the
//! caller falls through to the trace form (and, from there, fails closed).
//!
//! Deterministic by construction: a pure function of the problem and the
//! counterexample. No solver call, no wall clock, no sort default: an
//! unbound variable stays unbound and the validator rejects the derivation.
//! (The Unsafe verifier alone also tries a completing variant,
//! [`Counterexample::witness_ground_derivation_completed`].)

use super::Counterexample;
use crate::clause::HornClause;
use crate::ground_derivation::complete::{
    complete_env_for_clause_with_fallback, propagate_env_for_clause,
};
use crate::ground_derivation::{
    eval_ground_pub, validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem, ClauseHead};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl Counterexample {
    /// Whether the derivation witness, re-shaped into a ground derivation of
    /// `false`, validates against `problem` (see the module docs).
    pub(super) fn witness_ground_derivation_validates(&self, problem: &ChcProblem) -> bool {
        self.witness_ground_derivation(problem)
            .is_some_and(|derivation| validate_ground_derivation(problem, &derivation).is_ok())
    }

    /// The ground derivation the derivation witness names, or `None` when the
    /// witness does not name one (no witness, no query clause, a query that
    /// joins several predicates, an entry without an incoming clause, a
    /// premise-count mismatch or a cyclic premise graph).
    ///
    /// Steps are emitted in topological order (post-order from the root), and
    /// the violated query is appended as the final step with the root as its
    /// single premise.
    pub(crate) fn witness_ground_derivation(
        &self,
        problem: &ChcProblem,
    ) -> Option<GroundDerivation> {
        self.witness_ground_derivation_with(problem, false)
    }

    /// [`Self::witness_ground_derivation`], with the variables a step's
    /// witness values and equalities leave unbound filled by the bounded
    /// per-clause witness solve (`complete_env_for_clause_with_fallback`,
    /// under the caller's `ScopedWitnessChainBudget`). Value synthesis like
    /// the rest: only a derivation the validator accepts is evidence. Not for
    /// STEP D, which stays a deterministic, solver-free check.
    pub(crate) fn witness_ground_derivation_completed(
        &self,
        problem: &ChcProblem,
    ) -> Option<GroundDerivation> {
        self.witness_ground_derivation_with(problem, true)
    }

    fn witness_ground_derivation_with(
        &self,
        problem: &ChcProblem,
        complete: bool,
    ) -> Option<GroundDerivation> {
        let witness = self.witness.as_ref()?;
        let (candidates, recorded) = query_candidates(problem, witness)?;

        let mut steps: Vec<GroundDerivationStep> = Vec::new();
        let mut mapped: FxHashMap<usize, usize> = FxHashMap::default();
        let mut on_path: FxHashSet<usize> = FxHashSet::default();
        let mut stack = vec![(witness.root, false)];
        while let Some((entry_index, expanded)) = stack.pop() {
            if mapped.contains_key(&entry_index) {
                continue;
            }
            let entry = witness.entries.get(entry_index)?;
            if !expanded {
                // A repeated index on the current path is a cyclic witness.
                if !on_path.insert(entry_index) {
                    return None;
                }
                stack.push((entry_index, true));
                for &premise in entry.premises.iter().rev() {
                    if !mapped.contains_key(&premise) {
                        stack.push((premise, false));
                    }
                }
                continue;
            }
            on_path.remove(&entry_index);
            let clause_index = entry.incoming_clause?;
            let clause = problem.clauses().get(clause_index)?;
            if clause.is_query() || entry.premises.len() != clause.body.predicates.len() {
                return None;
            }
            let premises = entry
                .premises
                .iter()
                .map(|premise| mapped.get(premise).copied())
                .collect::<Option<Vec<usize>>>()?;
            let env = step_env(
                problem,
                &steps,
                clause,
                &entry.instances,
                &premises,
                complete,
            );
            mapped.insert(entry_index, steps.len());
            steps.push(GroundDerivationStep {
                clause_index,
                env,
                premises,
            });
        }

        let root_step = *mapped.get(&witness.root)?;
        let with_query = |query_index: usize| {
            let query_env = step_env(
                problem,
                &steps,
                &problem.clauses()[query_index],
                &FxHashMap::default(),
                &[root_step],
                complete,
            );
            let mut steps = steps.clone();
            let query_step = steps.len();
            steps.push(GroundDerivationStep {
                clause_index: query_index,
                env: query_env,
                premises: vec![root_step],
            });
            GroundDerivation { steps, query_step }
        };
        if recorded {
            return Some(with_query(candidates[0]));
        }
        candidates
            .into_iter()
            .map(with_query)
            .find(|derivation| validate_ground_derivation(problem, derivation).is_ok())
    }
}

/// The query clauses the witness's root may violate, and whether it is the
/// recorded one: the recorded query clause when it is a single-premise query
/// over the root's predicate, else (a transform-space index) every such query,
/// re-resolved by content. `None` when there is none.
fn query_candidates(
    problem: &ChcProblem,
    witness: &super::DerivationWitness,
) -> Option<(Vec<usize>, bool)> {
    let root = witness.entries.get(witness.root)?;
    let violates_root = |index: &usize| {
        problem.clauses().get(*index).is_some_and(|clause| {
            clause.is_query()
                && matches!(clause.body.predicates.as_slice(),
                    [(predicate, _)] if *predicate == root.predicate)
        })
    };
    if let Some(index) = witness.query_clause.filter(violates_root) {
        return Some((vec![index], true));
    }
    let candidates: Vec<usize> = (0..problem.clauses().len()).filter(violates_root).collect();
    (!candidates.is_empty()).then_some((candidates, false))
}

/// Candidate environment for one clause instance: the witness's own values
/// for the clause's variables, then each bare-variable body argument its
/// premise's head value, then whatever the clause's equalities determine,
/// then an undetermined bare-variable head argument the entry's value for it.
/// Earlier sources are never overwritten; the validator judges the result.
fn step_env(
    problem: &ChcProblem,
    steps: &[GroundDerivationStep],
    clause: &HornClause,
    instances: &FxHashMap<String, SmtValue>,
    premises: &[usize],
    complete: bool,
) -> FxHashMap<String, SmtValue> {
    let mut env = FxHashMap::default();
    for variable in clause.vars() {
        if let Some(value) = instances.get(&variable.name) {
            env.insert(variable.name, value.clone());
        }
    }
    for ((_, arguments), &premise) in clause.body.predicates.iter().zip(premises) {
        let Some(head_values) = premise_head_values(problem, steps.get(premise)) else {
            continue;
        };
        for (argument, value) in arguments.iter().zip(head_values) {
            if let (ChcExpr::Var(variable), Some(value)) = (argument, value) {
                env.entry(variable.name.clone()).or_insert(value);
            }
        }
    }
    propagate_env_for_clause(clause, &mut env);
    // A bare-variable head argument nothing above determined takes the
    // entry's value for that argument (its canonical `__p{pred}_a{i}`
    // instance): what the entry says the step derived.
    if let ClauseHead::Predicate(predicate, arguments) = &clause.head {
        let mut filled = false;
        for (index, argument) in arguments.iter().enumerate() {
            let canonical = crate::lemma_hints::canonical_var_name(*predicate, index);
            if let (ChcExpr::Var(variable), Some(value)) = (argument, instances.get(&canonical)) {
                if !env.contains_key(&variable.name) && value_fits_sort(value, &variable.sort) {
                    env.insert(variable.name.clone(), value.clone());
                    filled = true;
                }
            }
        }
        if filled {
            propagate_env_for_clause(clause, &mut env);
        }
    }
    if complete && clause.vars().iter().any(|var| !env.contains_key(&var.name)) {
        // The validator judges the result; a failed completion leaves gaps.
        let _ = complete_env_for_clause_with_fallback(clause, &mut env, instances);
    }
    env
}

/// Whether `value` can stand for a variable of `sort` (a gap filler only; the
/// validator's sort check stays authoritative).
fn value_fits_sort(value: &SmtValue, sort: &crate::ChcSort) -> bool {
    use crate::ChcSort;
    match (sort, value) {
        (ChcSort::Bool, SmtValue::Bool(_))
        | (ChcSort::Int, SmtValue::Int(_) | SmtValue::BigInt(_))
        | (ChcSort::Real, SmtValue::Real(_))
        | (ChcSort::Array(..), SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. })
        | (ChcSort::Datatype { .. }, SmtValue::Datatype(..)) => true,
        (ChcSort::BitVec(width), SmtValue::BitVec(_, w) | SmtValue::BigBitVec(_, w)) => width == w,
        _ => false,
    }
}

/// The head-argument values a premise step derives (`None` per argument that
/// does not evaluate), or `None` when the step or its clause is unavailable.
fn premise_head_values(
    problem: &ChcProblem,
    step: Option<&GroundDerivationStep>,
) -> Option<Vec<Option<SmtValue>>> {
    let step = step?;
    match &problem.clauses().get(step.clause_index)?.head {
        ClauseHead::Predicate(_, arguments) => Some(
            arguments
                .iter()
                .map(|argument| eval_ground_pub(argument, &step.env))
                .collect(),
        ),
        ClauseHead::False => None,
    }
}

#[cfg(test)]
mod tests;
