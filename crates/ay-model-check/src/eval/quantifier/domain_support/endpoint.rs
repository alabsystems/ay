// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-dependent range bounds, not a second general term evaluator.
//!
//! Int bounds remain literal/variable only. BV bounds additionally admit
//! same-width binary add/sub and genuine selector/select paths rooted in
//! concrete variables. Every variable differs from ALL unavailable binder
//! names; already installed outer values remain available. Each arithmetic
//! operand and complete receiver is authenticated before ordinary evaluation.

use super::{
    charge, EvalError, QuantifierRejection, SupportAnalysis, MAX_GUARDED_BITVEC_WIDTH,
    MAX_RANGE_BOUND_BITS, MAX_SUPPORT_DEPTH,
};
use crate::ModelValue;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

mod paths;
mod work;

impl SupportAnalysis<'_, '_> {
    pub(super) fn endpoint(&self, term: TermId) -> Result<Option<BigInt>, QuantifierRejection> {
        Ok(self.endpoint_value(term, 0)?.and_then(|value| match value {
            ModelValue::Int(value) | ModelValue::BitVec { value, .. } => Some(value),
            _ => None,
        }))
    }

    fn endpoint_value(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        charge(self.evaluator, 1)?;
        if depth > MAX_SUPPORT_DEPTH {
            return Err(QuantifierRejection::NestingLimit);
        }
        if self.evaluator.terms.sort(term) != self.sort {
            return Err(QuantifierRejection::BindingSortMismatch);
        }
        match self.evaluator.terms.get(term) {
            TermData::Const(constant) => {
                self.endpoint_literal_preflight(constant)?;
                self.endpoint_scalar(term, depth)
            }
            TermData::Var(name, _) => {
                charge(self.evaluator, name.len().div_ceil(64).max(1))?;
                // Even a different TermId with this name is shadowed. A
                // differently named OUTER binding, however, is a valid bound.
                if !self.endpoint_name_available(name)? {
                    return Ok(None);
                }
                self.endpoint_scalar(term, depth)
            }
            TermData::App(Symbol::Named(operator), args)
                if matches!(self.sort, Sort::BitVec(bitvec)
                    if (1..=MAX_GUARDED_BITVEC_WIDTH).contains(&bitvec.width)) =>
            {
                charge(self.evaluator, operator.len().div_ceil(64).max(1))?;
                if self.evaluator.terms.is_declared_function(operator) {
                    return Ok(None);
                }
                // Checked projections override even built-in arithmetic.
                // Decline rather than derive a bound for a different meaning.
                if self
                    .evaluator
                    .model
                    .projection_argument(term)
                    .map_err(|error| {
                        QuantifierRejection::UnevaluableBody(EvalError::Refused(error.to_string()))
                    })?
                    .is_some()
                {
                    return Ok(None);
                }
                match (operator.as_str(), args.as_slice()) {
                    ("bvadd" | "bvsub", [left, right]) => {
                        self.endpoint_binary(operator, *left, *right, depth)
                    }
                    ("select", [array, index]) => self.endpoint_select(term, *array, *index, depth),
                    (_, [argument]) => self.endpoint_selector(term, operator, *argument, depth),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    fn endpoint_name_available(&self, name: &str) -> Result<bool, QuantifierRejection> {
        if name == self.name {
            return Ok(false);
        }
        for (unavailable, _) in self.unavailable {
            charge(self.evaluator, unavailable.len().div_ceil(64).max(1))?;
            if name == unavailable {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn endpoint_literal_preflight(&self, constant: &Constant) -> Result<(), QuantifierRejection> {
        // Authenticate raw payload kind AND embedded width before eval_const
        // can normalize. A forged huge width with a tiny payload is not cheap.
        let value = match (constant, self.sort) {
            (Constant::Int(value), Sort::Int) => value,
            (Constant::BitVec { value, width }, Sort::BitVec(bitvec))
                if *width == bitvec.width && (1..=MAX_GUARDED_BITVEC_WIDTH).contains(width) =>
            {
                value
            }
            _ => return Err(QuantifierRejection::BindingSortMismatch),
        };
        self.endpoint_number_work(value)
    }

    fn endpoint_number_work(&self, value: &BigInt) -> Result<(), QuantifierRejection> {
        if value.bits() > MAX_RANGE_BOUND_BITS {
            return Err(QuantifierRejection::EvaluationBudget);
        }
        charge(self.evaluator, value.bits().div_ceil(64).max(1) as usize)
    }

    fn endpoint_scalar(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        let Some(value) = self.endpoint_evaluate(term, depth)? else {
            return Ok(None);
        };
        self.endpoint_validate_scalar(&value)?;
        Ok(Some(value))
    }

    /// Only genuine model absence is optional endpoint information. A hard
    /// evaluator failure must not become a whole-support atom that a sibling
    /// guard can discard, even when that sibling proves an empty support.
    fn endpoint_evaluate(
        &self,
        term: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        match self.evaluator.eval(term, self.eval_depth + depth + 1) {
            Ok(value) => Ok(Some(value)),
            Err(EvalError::ModelUnavailable(_)) => {
                charge(self.evaluator, 1)?;
                Ok(None)
            }
            Err(error) => Err(QuantifierRejection::UnevaluableBody(error)),
        }
    }

    fn endpoint_validate_scalar(&self, value: &ModelValue) -> Result<(), QuantifierRejection> {
        charge(self.evaluator, 1)?;
        self.evaluator
            .ensure_value_inhabits_sort(value, self.sort)
            .map_err(QuantifierRejection::UnevaluableBody)?;
        match value {
            ModelValue::Int(value) | ModelValue::BitVec { value, .. } => {
                self.endpoint_number_work(value)
            }
            _ => Err(QuantifierRejection::BindingSortMismatch),
        }
    }

    fn endpoint_binary(
        &self,
        operator: &str,
        left: TermId,
        right: TermId,
        depth: usize,
    ) -> Result<Option<ModelValue>, QuantifierRejection> {
        let Some(left) = self.endpoint_value(left, depth + 1)? else {
            return Ok(None);
        };
        let Some(right) = self.endpoint_value(right, depth + 1)? else {
            return Ok(None);
        };
        let Sort::BitVec(bitvec) = self.sort else {
            return Ok(None);
        };
        // Both operands are already normalized, typed, and at most 128 bits.
        // Addition/subtraction plus width normalization takes linear limb work.
        charge(self.evaluator, 8 * bitvec.width.div_ceil(64) as usize)?;
        let result = crate::bitvec::eval_named(operator, &[left, right])
            .map_err(|error| QuantifierRejection::UnevaluableBody(EvalError::from(error)))?;
        self.endpoint_validate_scalar(&result)?;
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests;
