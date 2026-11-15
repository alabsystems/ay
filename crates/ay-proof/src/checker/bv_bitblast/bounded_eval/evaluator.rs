// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::ToPrimitive;

pub(super) struct Evaluator<'a, 'p, E> {
    pub(super) terms: &'a TermStore,
    pub(super) env: &'a [(TermId, EvalValue)],
    pub(super) control: &'p mut dyn FnMut() -> Result<(), E>,
}

impl<E> Evaluator<'_, '_, E> {
    pub(super) fn poll(&mut self) -> EvalResult<(), E> {
        (self.control)().map_err(EvalError::Interrupted)
    }

    pub(super) fn term(&mut self, term: TermId) -> EvalResult<EvalValue, E> {
        self.poll()?;
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Ok(EvalValue::Bool(*value)),
            TermData::Const(Constant::BitVec { value, width }) => {
                let value = value.to_u64().ok_or(EvalError::Unsupported)? & bv_mask(*width);
                Ok(EvalValue::BitVec {
                    value,
                    width: *width,
                })
            }
            TermData::Var(_, _) => {
                let env = self.env;
                for &(variable, value) in env {
                    self.poll()?;
                    if variable == term {
                        return Ok(value);
                    }
                }
                Err(EvalError::Unsupported)
            }
            TermData::Not(inner) => Ok(EvalValue::Bool(!self.boolean(*inner)?)),
            TermData::Ite(condition, then_term, else_term) => {
                let branch = if self.boolean(*condition)? {
                    *then_term
                } else {
                    *else_term
                };
                self.term(branch)
            }
            TermData::App(symbol, args) => self.app(symbol, args),
            _ => Err(EvalError::Unsupported),
        }
    }

    pub(super) fn boolean(&mut self, term: TermId) -> EvalResult<bool, E> {
        match self.term(term)? {
            EvalValue::Bool(value) => Ok(value),
            EvalValue::BitVec { .. } => Err(EvalError::Unsupported),
        }
    }

    pub(super) fn bitvector(&mut self, term: TermId) -> EvalResult<(u64, u32), E> {
        match self.term(term)? {
            EvalValue::BitVec { value, width } => Ok((value & bv_mask(width), width)),
            EvalValue::Bool(_) => Err(EvalError::Unsupported),
        }
    }

    pub(super) fn same_width(&mut self, args: &[TermId]) -> EvalResult<(u64, u64, u32), E> {
        let (left, left_width) = self.bitvector(args[0])?;
        let (right, right_width) = self.bitvector(args[1])?;
        if left_width == right_width {
            Ok((left, right, left_width))
        } else {
            Err(EvalError::Unsupported)
        }
    }
}
