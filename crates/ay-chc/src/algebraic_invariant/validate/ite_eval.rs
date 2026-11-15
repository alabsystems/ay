// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `ite` evaluation for the algebraic validator's syntactic fast path.
//!
//! An `ite` whose condition the environment cannot decide has a value when
//! both branches agree, or when they agree after peeling a same-condition
//! `ite` out of each: under `c`, `(ite c a b)` in the then branch is `a`, and
//! under `(not c)` one in the else branch is `b`.
//!
//! The peel used to evaluate its branches from scratch. A branch with nothing
//! to peel selects itself, so every undecided `ite` paid for both of its
//! branches twice, `2^depth` evaluations on an `ite` chain; a branch that is a
//! same-condition `ite` selects a grandchild the branch's own evaluation had
//! just computed, so a chain of same-condition `ite`s paid Fibonacci-many. The
//! fast path polls no budget inside one formula, so either shape held the
//! algebraic pre-strategy past its deadline and past an external cancellation:
//! a 13-deep 8-bit chain (MODEL_CHECKER_CONSUMER ask 2026-10-14-acyclic-8bit-ite-chain)
//! took five and a half minutes. Each branch evaluation now returns its own
//! branch results with its value and the peel reads them, so each `ite` node of
//! a tree-shaped term is evaluated once.
//!
//! A subterm shared between branches is still walked once per path. Each
//! recursive operation observes the same invocation-local budget, and an
//! interrupted branch contributes no value or condition key.

use super::{
    budget, validation_bool_result_checked, validation_expr_key_checked, SynthesisBudget,
    ValidationInterval, ValidationResult,
};
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

/// A branch's [`validation_bool_result_checked`] and, for an `ite` whose condition was
/// undecided, the results of its own then and else branches.
#[derive(Clone, Copy)]
pub(super) struct ValidationIteEval {
    pub(super) value: Option<bool>,
    branches: Option<(Option<bool>, Option<bool>)>,
}

impl ValidationIteEval {
    fn plain(value: Option<bool>) -> Self {
        Self {
            value,
            branches: None,
        }
    }

    /// The result of the then branch (`true`) or the else branch (`false`),
    /// when this evaluation computed it.
    fn branch(self, condition_value: bool) -> Option<Option<bool>> {
        self.branches.map(|(then_value, else_value)| {
            if condition_value {
                then_value
            } else {
                else_value
            }
        })
    }
}

/// [`validation_bool_result_checked`] of the simplified `ite` whose arguments are
/// `args`.
pub(super) fn validation_ite_eval_checked(
    args: &[Arc<ChcExpr>],
    int_env: &FxHashMap<String, ValidationInterval>,
    bool_env: &FxHashMap<String, bool>,
    residue_env: &FxHashMap<String, (i128, i128)>,
    budget: &SynthesisBudget,
) -> ValidationResult<ValidationIteEval> {
    budget::run(budget, || {
        if let Some(condition) = validation_bool_result_checked(
            args[0].as_ref(),
            int_env,
            bool_env,
            residue_env,
            budget,
        )? {
            return Ok(ValidationIteEval::plain(validation_bool_result_checked(
                args[if condition { 1 } else { 2 }].as_ref(),
                int_env,
                bool_env,
                residue_env,
                budget,
            )?));
        }
        let then_eval = validation_branch_eval_checked(
            args[1].as_ref(),
            int_env,
            bool_env,
            residue_env,
            budget,
        )?;
        let else_eval = validation_branch_eval_checked(
            args[2].as_ref(),
            int_env,
            bool_env,
            residue_env,
            budget,
        )?;
        let value = if then_eval.value.is_some() && then_eval.value == else_eval.value {
            then_eval.value
        } else {
            validation_same_condition_nested_ite_result_checked(
                args[0].as_ref(),
                (args[1].as_ref(), then_eval),
                (args[2].as_ref(), else_eval),
                int_env,
                bool_env,
                residue_env,
                budget,
            )?
        };
        Ok(ValidationIteEval {
            value,
            branches: Some((then_eval.value, else_eval.value)),
        })
    })
}

/// [`validation_bool_result_checked`] of `expr`, keeping the branch results when it
/// simplifies to an `ite`: `validation_bool_result` would simplify `expr` and
/// hand that `ite` to [`validation_ite_eval_checked`], which is what this does.
fn validation_branch_eval_checked(
    expr: &ChcExpr,
    int_env: &FxHashMap<String, ValidationInterval>,
    bool_env: &FxHashMap<String, bool>,
    residue_env: &FxHashMap<String, (i128, i128)>,
    budget: &SynthesisBudget,
) -> ValidationResult<ValidationIteEval> {
    budget::run(budget, || {
        if matches!(expr, ChcExpr::Op(ChcOp::Ite, _)) {
            if let ChcExpr::Op(ChcOp::Ite, args) = &budget::simplify(expr, budget)? {
                if args.len() == 3 {
                    return validation_ite_eval_checked(
                        args,
                        int_env,
                        bool_env,
                        residue_env,
                        budget,
                    );
                }
            }
        }
        Ok(ValidationIteEval::plain(validation_bool_result_checked(
            expr,
            int_env,
            bool_env,
            residue_env,
            budget,
        )?))
    })
}

/// Decides an undecided-condition `ite` by peeling a same-condition `ite` out
/// of each branch. A branch with nothing to peel contributes its own value; a
/// peeled branch contributes its selected branch's result, which its own
/// evaluation computed.
fn validation_same_condition_nested_ite_result_checked(
    condition: &ChcExpr,
    (then_expr, then_eval): (&ChcExpr, ValidationIteEval),
    (else_expr, else_eval): (&ChcExpr, ValidationIteEval),
    int_env: &FxHashMap<String, ValidationInterval>,
    bool_env: &FxHashMap<String, bool>,
    residue_env: &FxHashMap<String, (i128, i128)>,
    budget: &SynthesisBudget,
) -> ValidationResult<Option<bool>> {
    budget::run(budget, || {
        let condition_key = validation_expr_key_checked(condition, budget)?;
        let then_selected = validation_nested_ite_branch_for_condition_checked(
            then_expr,
            &condition_key,
            true,
            budget,
        )?;
        let else_selected = validation_nested_ite_branch_for_condition_checked(
            else_expr,
            &condition_key,
            false,
            budget,
        )?;
        if then_selected.is_none() && else_selected.is_none() {
            // Nothing to peel: the caller already compared these two values.
            return Ok(None);
        }
        let peeled = |selected: Option<&ChcExpr>,
                      eval: ValidationIteEval,
                      condition_value|
         -> ValidationResult<Option<bool>> {
            let Some(selected) = selected else {
                return Ok(eval.value);
            };
            match eval.branch(condition_value) {
                Some(value) => Ok(value),
                None => {
                    validation_bool_result_checked(selected, int_env, bool_env, residue_env, budget)
                }
            }
        };
        let Some(then_result) = peeled(then_selected, then_eval, true)? else {
            return Ok(None);
        };
        let Some(else_result) = peeled(else_selected, else_eval, false)? else {
            return Ok(None);
        };
        Ok((then_result == else_result).then_some(then_result))
    })
}

/// The branch of `expr` that `condition_value` selects, when `expr` is an
/// `ite` on the condition whose key is `condition_key`.
fn validation_nested_ite_branch_for_condition_checked<'a>(
    expr: &'a ChcExpr,
    condition_key: &str,
    condition_value: bool,
    budget: &SynthesisBudget,
) -> ValidationResult<Option<&'a ChcExpr>> {
    budget::run(budget, || {
        let ChcExpr::Op(ChcOp::Ite, args) = expr else {
            return Ok(None);
        };
        if args.len() != 3
            || validation_expr_key_checked(args[0].as_ref(), budget)? != condition_key
        {
            return Ok(None);
        }
        Ok(Some(args[if condition_value { 1 } else { 2 }].as_ref()))
    })
}

#[cfg(test)]
mod tests;
