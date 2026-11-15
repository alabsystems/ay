// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! Frozen evaluator from 6341cb2ab. No controlled evaluator or live arithmetic
//! helper is used. Only the long application dispatch is mechanically split.

use super::{
    Constant, EvalValue, EvalVar, EvalVarKind, ProofCheckError, ProofId, Sort, Symbol, TermData,
    TermId, TermStore,
};
use num_traits::ToPrimitive;

mod app;
mod collect;
mod indexed;
mod numeric;

use app::eval_app;
use collect::collect_bounded_vars;
use indexed::eval_indexed_bv;
use numeric::{bv_mask, eval_bv_shift, eval_bv_signed_divrem, to_signed_u64};

const MAX_BOUNDED_ASSIGNMENT_BITS: u32 = 8;
const MAX_EVALUATED_BV_WIDTH: u32 = 64;
const MAX_BOUNDED_BV_WIDTH: u32 = 4;

pub(super) fn validate(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let Some(vars) = collect_bounded_vars(terms, clause) else {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "bv_bitblast clause contains unsupported or too-wide \
                     Bool/BV terms; strict mode only accepts lemmas it can \
                     exhaustively evaluate"
                .to_string(),
        });
    };
    let total_bits = vars
        .iter()
        .try_fold(0_u32, |total, var| total.checked_add(var.bits))
        .ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "bv_bitblast bounded-variable width sum overflows u32".to_string(),
        })?;
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
        let env = build_eval_env(&vars, assignment);
        let mut clause_true = false;
        for &lit in clause {
            let Some(value) = eval_bool_term(terms, lit, &env) else {
                return Err(ProofCheckError::InvalidTheoryLemma {
                    step: step_id,
                    reason: "bv_bitblast clause contains a literal the strict \
                             bounded checker cannot evaluate"
                        .to_string(),
                });
            };
            if value {
                clause_true = true;
                break;
            }
        }
        if !clause_true {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: "bv_bitblast clause is falsified by a bounded Bool/BV \
                         assignment"
                    .to_string(),
            });
        }
    }

    Ok(())
}

fn build_eval_env(vars: &[EvalVar], assignment: u64) -> Vec<(TermId, EvalValue)> {
    let mut env = Vec::with_capacity(vars.len());
    let mut remaining = assignment;
    for var in vars {
        match var.kind {
            EvalVarKind::Bool => {
                env.push((var.term, EvalValue::Bool((remaining & 1) != 0)));
                remaining >>= 1;
            }
            EvalVarKind::BitVec => {
                let mask = bv_mask(var.bits);
                env.push((
                    var.term,
                    EvalValue::BitVec {
                        value: remaining & mask,
                        width: var.bits,
                    },
                ));
                remaining >>= var.bits;
            }
        }
    }
    env
}

fn eval_bool_term(terms: &TermStore, term: TermId, env: &[(TermId, EvalValue)]) -> Option<bool> {
    match eval_term(terms, term, env)? {
        EvalValue::Bool(value) => Some(value),
        EvalValue::BitVec { .. } => None,
    }
}

pub(super) fn eval_term(
    terms: &TermStore,
    term: TermId,
    env: &[(TermId, EvalValue)],
) -> Option<EvalValue> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(EvalValue::Bool(*value)),
        TermData::Const(Constant::BitVec { value, width }) => {
            let value = value.to_u64()? & bv_mask(*width);
            Some(EvalValue::BitVec {
                value,
                width: *width,
            })
        }
        TermData::Var(_, _) => env
            .iter()
            .find_map(|(var, value)| (*var == term).then_some(*value)),
        TermData::Not(inner) => Some(EvalValue::Bool(!eval_bool_term(terms, *inner, env)?)),
        TermData::Ite(c, t, e) => {
            let branch = if eval_bool_term(terms, *c, env)? {
                *t
            } else {
                *e
            };
            eval_term(terms, branch, env)
        }
        TermData::App(sym, args) => eval_app(terms, sym, args, env),
        _ => None,
    }
}

fn eval_bv_arg(terms: &TermStore, arg: TermId, env: &[(TermId, EvalValue)]) -> Option<(u64, u32)> {
    match eval_term(terms, arg, env)? {
        EvalValue::BitVec { value, width } => Some((value & bv_mask(width), width)),
        EvalValue::Bool(_) => None,
    }
}

fn eval_same_width_bv_args(
    terms: &TermStore,
    args: &[TermId],
    env: &[(TermId, EvalValue)],
) -> Option<(u64, u64, u32)> {
    let (lhs, lhs_width) = eval_bv_arg(terms, args[0], env)?;
    let (rhs, rhs_width) = eval_bv_arg(terms, args[1], env)?;
    (lhs_width == rhs_width).then_some((lhs, rhs, lhs_width))
}
