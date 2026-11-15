// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The init-to-bad trace a validated LINEAR ground derivation derives, and
//! the two places a counterexample's `steps` must agree with it.
//!
//! A validated [`GroundDerivation`] is what confirms UNSAFE (the verifier's
//! fast path and STEP D both accept on it), but the certificate and the
//! trace-validity obligation are read off `steps`, a separate field that no
//! check compared with the derivation. The clause-inlining back-translator
//! re-maps the engine's steps without re-inserting the states of inlined
//! predicates, while its ground-derivation translator expands the inlined
//! clauses. The published steps then stopped short of the derivation (7 steps
//! against 8 derived states for `S(0,x,c) -> S(-2,x,c) -> false` with the
//! abort location inlined into the query), and `ay --stats` exported a
//! `trace-validity-depth-6` obligation, `expected-result: sat`, that z3
//! refutes, next to a strict `unsat` that STEP D confirmed from the
//! derivation.
//!
//! - [`Counterexample::restated_by_derivation`]: what the verifier publishes
//!   when it accepts on the derivation is the trace the derivation derives.
//! - [`Counterexample::refuse_unbacked_trace_validity`]: the exporter refuses
//!   an obligation whose steps contradict the counterexample's own validated
//!   derivation, whichever path built the counterexample.
//!
//! Pure functions of the problem and the counterexample: no solver call, no
//! wall clock. A non-linear derivation derives no single trace, and nothing
//! is compared or restated for it.

use super::{Counterexample, CounterexampleStep, TraceValidity};
use crate::ground_derivation::{eval_ground_pub, validate_ground_derivation, GroundDerivation};
use crate::smt::SmtValue;
use crate::transition_system::TransitionSystem;
use crate::{ChcError, ChcProblem, ChcResult, ClauseHead, PredicateId};
use std::borrow::Cow;

/// One state of a derived trace: the fact the step's clause concludes.
struct DerivedState {
    predicate: PredicateId,
    clause_index: usize,
    /// The clause's head arguments evaluated under the step's assignment.
    values: Vec<SmtValue>,
}

impl Counterexample {
    /// This counterexample with the steps `derivation` derives, when its own
    /// steps claim a different trace; `None` when they agree, when it claims
    /// no trace (no steps), or when `derivation` is not a linear chain.
    ///
    /// REQUIRES: `derivation` validates against `problem` (the caller decided
    /// UNSAFE on it). Agreement is: the same number of states, the same
    /// predicates, and every canonical (`__p{pred}_a{k}`) assignment the steps
    /// hold equal to the derived argument value. The restated counterexample
    /// keeps the derivation and drops the witness, which was not what was
    /// verified and names the trace the steps claimed.
    pub(crate) fn restated_by_derivation(
        &self,
        problem: &ChcProblem,
        derivation: &GroundDerivation,
    ) -> Option<Self> {
        if self.steps.is_empty() {
            return None;
        }
        let states = derived_states(problem, derivation)?;
        let agrees = self.steps.len() == states.len()
            && self.steps.iter().zip(&states).all(|(step, state)| {
                step.predicate == state.predicate
                    && state.values.iter().enumerate().all(|(arg, value)| {
                        step.assignments
                            .get(&crate::lemma_hints::canonical_var_name(
                                state.predicate,
                                arg,
                            ))
                            .is_none_or(|raw| trace_raw_value(value) == Some(*raw))
                    })
            });
        if agrees {
            return None;
        }
        Some(Self::trace_of(problem, &states, derivation))
    }

    /// The counterexample whose steps are the trace `derivation` derives,
    /// carrying `derivation`; `None` when it is not a linear chain. For a
    /// counterexample built from a derivation alone, which claims no trace
    /// that [`Self::restated_by_derivation`] could restate.
    ///
    /// REQUIRES: `derivation` validates against `problem`.
    pub(crate) fn traced_by_derivation(
        problem: &ChcProblem,
        derivation: &GroundDerivation,
    ) -> Option<Self> {
        let states = derived_states(problem, derivation)?;
        Some(Self::trace_of(problem, &states, derivation))
    }

    fn trace_of(
        problem: &ChcProblem,
        states: &[DerivedState],
        derivation: &GroundDerivation,
    ) -> Self {
        let steps = states
            .iter()
            .map(|state| {
                let assignments = state
                    .values
                    .iter()
                    .enumerate()
                    .filter_map(|(arg, value)| {
                        let name = crate::lemma_hints::canonical_var_name(state.predicate, arg);
                        trace_raw_value(value).map(|raw| (name, raw))
                    })
                    .collect();
                let step = CounterexampleStep::new(state.predicate, assignments)
                    .with_clause(state.clause_index);
                match problem.clause_action(state.clause_index) {
                    Some(action) => step.with_action(action),
                    None => step,
                }
            })
            .collect();
        Self {
            steps,
            witness: None,
            compact_derivation: None,
            ground_derivation: Some(derivation.clone()),
        }
    }

    /// Refuse to export `trace` when what this counterexample carries
    /// contradicts it: its pins ground-evaluate the obligation to `false` (the
    /// 069f4e5f4 guard), or its steps disagree with the counterexample's
    /// validated linear ground derivation (attached, else the one its witness
    /// names) in length or in a pinned value, so the obligation is not the
    /// trace that was verified. An obligation its pins decide `true` exports,
    /// and so does one with no validated linear derivation to compare with.
    pub(super) fn refuse_unbacked_trace_validity(
        &self,
        problem: &ChcProblem,
        trace: &TraceValidity,
    ) -> ChcResult<()> {
        let refuse = |reason: String| {
            Err(ChcError::Verification(format!(
                "cannot export unsafe trace-validity replay obligation: {reason}"
            )))
        };
        match eval_ground_pub(&trace.formula, &trace.env) {
            Some(SmtValue::Bool(true)) => return Ok(()),
            Some(SmtValue::Bool(false)) => {
                return refuse(format!(
                    "the trace's concrete assignments ground-evaluate the depth-{} \
                     obligation to false",
                    trace.depth
                ));
            }
            _ => {}
        }
        let Some(states) = self
            .backing_derivation(problem)
            .and_then(|derivation| derived_states(problem, &derivation))
        else {
            return Ok(());
        };
        if states.len() != trace.depth + 1 {
            return refuse(format!(
                "the trace has {} steps but the counterexample's validated ground \
                 derivation derives {} states",
                trace.depth + 1,
                states.len()
            ));
        }
        for (time, state) in states.iter().enumerate() {
            if state.predicate != trace.ts.predicate {
                return refuse(format!(
                    "the counterexample's validated ground derivation derives predicate \
                     {} at step {time}",
                    state.predicate
                ));
            }
            for (var, derived) in trace.ts.state_vars().iter().zip(&state.values) {
                let name = TransitionSystem::version_var(var, time).name;
                if let Some(pinned) = trace.env.get(&name).filter(|pinned| *pinned != derived) {
                    return refuse(format!(
                        "step {time} pins {name} = {pinned:?}, but the counterexample's \
                         validated ground derivation derives {derived:?}"
                    ));
                }
            }
        }
        Ok(())
    }

    /// The ground derivation that confirms this counterexample on `problem`:
    /// the attached one if it validates, else the one its witness names if
    /// that validates (the two forms STEP D accepts on).
    fn backing_derivation(&self, problem: &ChcProblem) -> Option<Cow<'_, GroundDerivation>> {
        if let Some(derivation) = &self.ground_derivation {
            if validate_ground_derivation(problem, derivation).is_ok() {
                return Some(Cow::Borrowed(derivation));
            }
        }
        self.witness_ground_derivation(problem)
            .filter(|derivation| validate_ground_derivation(problem, derivation).is_ok())
            .map(Cow::Owned)
    }
}

/// The init-to-bad states of `derivation` when it is a linear chain (the
/// query step has one premise, every step below it at most one); `None`
/// otherwise, or when a head argument does not evaluate to a concrete value.
fn derived_states(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Option<Vec<DerivedState>> {
    let query = derivation.steps.get(derivation.query_step)?;
    let &[root] = query.premises.as_slice() else {
        return None;
    };
    let mut current = root;
    let mut states = Vec::new();
    loop {
        // Validated premises point strictly backwards; the cap keeps the walk
        // total on any input.
        if states.len() >= derivation.steps.len() {
            return None;
        }
        let step = derivation.steps.get(current)?;
        let ClauseHead::Predicate(predicate, args) =
            &problem.clauses().get(step.clause_index)?.head
        else {
            return None;
        };
        let values = args
            .iter()
            .map(|arg| eval_ground_pub(arg, &step.env))
            .collect::<Option<Vec<_>>>()?;
        states.push(DerivedState {
            predicate: *predicate,
            clause_index: step.clause_index,
            values,
        });
        match step.premises.as_slice() {
            [] => break,
            &[premise] => current = premise,
            _ => return None,
        }
    }
    states.reverse();
    Some(states)
}

/// A derived value as a `CounterexampleStep` assignment (the `i64` boundary
/// the exporter reads back through `trace_value_smt`); `None` when it has no
/// such form (the step then omits it and the exporter fails closed).
fn trace_raw_value(value: &SmtValue) -> Option<i64> {
    use num_traits::ToPrimitive;
    match value {
        SmtValue::Bool(value) => Some(i64::from(*value)),
        SmtValue::Int(value) => i64::try_from(*value).ok(),
        SmtValue::BitVec(value, _) => i64::try_from(*value).ok(),
        SmtValue::BigBitVec(value, _) => value.to_i64(),
        SmtValue::Real(value) if value.is_integer() => value.to_integer().to_i64(),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
