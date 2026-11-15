// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cancellation points in the existing exhaustive Bool/BV interpretation.
//!
//! Polling does not change the assignment space, recursively reevaluate the
//! classifier, or memoize expressions. Individual allocation, hashing, integer
//! conversion and fixed-width arithmetic operations remain opaque intervals.

use super::{
    bv_mask, classification, eval_bv_shift, eval_bv_signed_divrem, to_signed_u64, Constant,
    EvalValue, EvalVar, EvalVarKind, ProofCheckError, ProofId, Symbol, TermData, TermId, TermStore,
    MAX_BOUNDED_ASSIGNMENT_BITS, MAX_EVALUATED_BV_WIDTH,
};

mod app;
mod evaluator;
mod indexed;

use evaluator::Evaluator;

#[derive(Debug, PartialEq, Eq)]
enum EvalError<E> {
    Unsupported,
    Interrupted(E),
}

type EvalResult<T, E> = Result<T, EvalError<E>>;

pub(super) fn validate(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    poll: &mut dyn FnMut() -> Result<(), ProofCheckError>,
) -> Result<(), ProofCheckError> {
    poll()?;
    // One classification walk for this evaluation, using the same control.
    let vars = classification::bounded_vars(terms, clause, poll)?;
    poll()?;
    let vars = vars.ok_or_else(|| {
        invalid(
            step_id,
            "bv_bitblast clause contains unsupported or too-wide \
        Bool/BV terms; strict mode only accepts lemmas it can \
        exhaustively evaluate",
        )
    })?;
    let mut total_bits = 0_u32;
    for var in &vars {
        poll()?;
        total_bits = total_bits.checked_add(var.bits).ok_or_else(|| {
            invalid(
                step_id,
                "bv_bitblast bounded-variable width sum overflows u32",
            )
        })?;
    }
    if total_bits > MAX_BOUNDED_ASSIGNMENT_BITS {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!(
                "bv_bitblast clause needs {total_bits} assignment bits, \
                above strict bounded checker limit {MAX_BOUNDED_ASSIGNMENT_BITS}"
            ),
        });
    }
    let assignment_count = 1u64 << total_bits;
    for assignment in 0..assignment_count {
        poll()?;
        let env = build_env(&vars, assignment, poll)?;
        let mut clause_true = false;
        for &literal in clause {
            poll()?;
            let value = match evaluate(terms, literal, &env, poll) {
                Ok(EvalValue::Bool(value)) => value,
                Err(EvalError::Interrupted(error)) => return Err(error),
                Ok(EvalValue::BitVec { .. }) | Err(EvalError::Unsupported) => {
                    return Err(invalid(
                        step_id,
                        "bv_bitblast clause contains a literal the strict \
                        bounded checker cannot evaluate",
                    ));
                }
            };
            if value {
                clause_true = true;
                break;
            }
        }
        // Include environment disposal in the boundary before admission of
        // this assignment, while leaving the allocator operation itself opaque.
        drop(env);
        poll()?;
        if !clause_true {
            return Err(invalid(
                step_id,
                "bv_bitblast clause is falsified by a bounded Bool/BV \
                assignment",
            ));
        }
    }
    drop(vars);
    poll()?;
    Ok(())
}

/// Whether [`validate`] refuses `clause` right after its classification walk,
/// before a single assignment is enumerated: a node it cannot evaluate (a
/// variable wider than its per-variable bound, an unsupported operator), or
/// more than `MAX_BOUNDED_ASSIGNMENT_BITS` assignment bits in all. The walk is
/// the same visited-DAG walk [`validate`] performs, stopping at the first
/// refusing node.
pub(super) fn refuses_before_evaluating(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut never_stop = || Ok::<(), std::convert::Infallible>(());
    match classification::bounded_vars(terms, clause, &mut never_stop) {
        Ok(Some(vars)) => vars
            .iter()
            .try_fold(0_u32, |bits, var| bits.checked_add(var.bits))
            .is_none_or(|bits| bits > MAX_BOUNDED_ASSIGNMENT_BITS),
        Ok(None) => true,
        Err(never) => match never {},
    }
}

fn invalid(step: ProofId, reason: &str) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: reason.to_owned(),
    }
}

fn build_env<E>(
    vars: &[EvalVar],
    assignment: u64,
    poll: &mut dyn FnMut() -> Result<(), E>,
) -> Result<Vec<(TermId, EvalValue)>, E> {
    poll()?;
    let mut env = Vec::with_capacity(vars.len());
    let mut remaining = assignment;
    for var in vars {
        poll()?;
        let value = match var.kind {
            EvalVarKind::Bool => {
                let value = EvalValue::Bool((remaining & 1) != 0);
                remaining >>= 1;
                value
            }
            EvalVarKind::BitVec => {
                let value = EvalValue::BitVec {
                    value: remaining & bv_mask(var.bits),
                    width: var.bits,
                };
                remaining >>= var.bits;
                value
            }
        };
        env.push((var.term, value));
    }
    poll()?;
    Ok(env)
}

fn evaluate<E>(
    terms: &TermStore,
    term: TermId,
    env: &[(TermId, EvalValue)],
    poll: &mut dyn FnMut() -> Result<(), E>,
) -> EvalResult<EvalValue, E> {
    let mut evaluator = Evaluator {
        terms,
        env,
        control: poll,
    };
    let result = evaluator.term(term);
    // Never poll again after refusal. Unsupported is not refusal, and gets
    // the same final boundary before its caller may consider another route.
    if !matches!(&result, Err(EvalError::Interrupted(_))) {
        evaluator.poll()?;
    }
    result
}

/// Evaluation steps admitted for one closed term in [`closed_bv_in`].
const MAX_CLOSED_BV_POLLS: u32 = 4_096;

/// The value of a bit-vector term CLOSED once the variables of `env` are
/// read as their values, under the exhaustive interpretation [`validate`]
/// itself uses, or `None` when the term mentions another variable or an
/// operator the evaluator does not interpret, or needs more than
/// `MAX_CLOSED_BV_POLLS` steps (the walk shares no memo, so the cap bounds a
/// deeply shared DAG too).
///
/// The proof-producing lowering asks this for a DIVISOR: SMT-LIB's own
/// `bvsdiv` definition divides by `(bvneg t)`, so the definitional spelling
/// of external-codegen's `SDIV Xd, Xn, #-1` divides by the closed `(bvneg #xff..)`,
/// which is `1` — a shift by zero, not a general division. `env` holds the
/// constants a lemma's own hypothesis or case fixes (`hypotheses.rs`,
/// `case_split.rs`), under which those variables are exactly those values.
pub(super) fn closed_bv_in(
    terms: &TermStore,
    term: TermId,
    env: &[(TermId, EvalValue)],
) -> Option<u64> {
    let mut remaining = MAX_CLOSED_BV_POLLS;
    let mut poll = || -> Result<(), ()> {
        remaining = remaining.checked_sub(1).ok_or(())?;
        Ok(())
    };
    match evaluate(terms, term, env, &mut poll) {
        Ok(EvalValue::BitVec { value, .. }) => Some(value),
        _ => None,
    }
}

#[cfg(test)]
fn evaluate_legacy(
    terms: &TermStore,
    term: TermId,
    env: &[(TermId, EvalValue)],
) -> Option<EvalValue> {
    use std::convert::Infallible;
    match evaluate(terms, term, env, &mut || Ok::<(), Infallible>(())) {
        Ok(value) => Some(value),
        Err(EvalError::Unsupported) => None,
        Err(EvalError::Interrupted(never)) => match never {},
    }
}

#[cfg(test)]
mod tests;
