// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-query evaluation of sequence power, separate from independent checking.

use super::{EvalValue, Executor, Model};
use ay_core::{Sort, TermId};
use num_traits::{Signed, ToPrimitive, Zero};

impl Executor {
    pub(super) fn evaluate_seq_power(&self, model: &Model, args: &[TermId]) -> EvalValue {
        let [base, count] = args else {
            return EvalValue::Unknown;
        };
        let EvalValue::Rational(exponent) = self.evaluate_term(model, *count) else {
            return EvalValue::Unknown;
        };
        if !exponent.is_integer() {
            return EvalValue::Unknown;
        }
        let exponent = exponent.to_integer();
        if exponent.is_negative() || exponent.is_zero() {
            return match self.ctx.terms.sort(*base) {
                Sort::String => EvalValue::String(String::new()),
                Sort::Seq(_) => EvalValue::Seq(Vec::new()),
                _ => EvalValue::Unknown,
            };
        }
        let value = self.evaluate_term(model, *base);
        let length = match &value {
            EvalValue::String(word) => word.len(),
            EvalValue::Seq(elements) => elements.len(),
            _ => return EvalValue::Unknown,
        };
        if length == 0 {
            return value;
        }
        let Some(copies) = exponent.to_usize() else {
            return EvalValue::Unknown;
        };
        let Some(output_length) = length.checked_mul(copies) else {
            return EvalValue::Unknown;
        };
        if output_length > (1 << 20) {
            return EvalValue::Unknown;
        }
        match value {
            EvalValue::String(word) => EvalValue::String(word.repeat(copies)),
            EvalValue::Seq(elements) => {
                let mut output = Vec::with_capacity(output_length);
                for _ in 0..copies {
                    output.extend_from_slice(&elements);
                }
                EvalValue::Seq(output)
            }
            _ => EvalValue::Unknown,
        }
    }
}
