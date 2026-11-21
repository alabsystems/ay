// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual operand-magnitude admission before native bigint/rational operations
//! reached while computing a symbolic body. No fresh work owner is created.

use super::*;

impl Evaluator<'_> {
    pub(in crate::eval) fn admit_symbolic_value_scratch(&self, count: usize) -> EvalResult<()> {
        if self.symbolic_active.borrow().is_empty() {
            return Ok(());
        }
        self.admit_evaluation(
            count,
            count
                .checked_mul(std::mem::size_of::<ModelValue>())
                .ok_or("symbolic operand storage overflow")?,
        )
    }

    pub(in crate::eval) fn admit_symbolic_arithmetic(
        &self,
        values: &[ModelValue],
    ) -> EvalResult<()> {
        if self.symbolic_active.borrow().is_empty() {
            return Ok(());
        }
        self.admit_evaluation(
            values.len(),
            values
                .len()
                .checked_mul(std::mem::size_of::<&ModelValue>())
                .ok_or("symbolic operand reference overflow")?,
        )?;
        let mut borrowed = Vec::new();
        borrowed
            .try_reserve_exact(values.len())
            .map_err(|_| "symbolic arithmetic admission allocation refused")?;
        borrowed.extend(values.iter());
        self.admit_symbolic_numeric_work(&borrowed)
    }

    pub(in crate::eval) fn admit_symbolic_array_read(
        &self,
        array: &ArrayValue,
        index: &ModelValue,
    ) -> EvalResult<()> {
        if self.symbolic_active.borrow().is_empty() {
            return Ok(());
        }
        let count = array
            .store
            .len()
            .checked_add(1)
            .ok_or("symbolic array key overflow")?;
        self.admit_evaluation(
            count,
            count
                .checked_mul(std::mem::size_of::<&ModelValue>())
                .ok_or("symbolic array key storage overflow")?,
        )?;
        let mut keys = Vec::new();
        keys.try_reserve_exact(count)
            .map_err(|_| "symbolic array key admission allocation refused")?;
        keys.push(index);
        keys.extend(array.store.iter().map(|(key, _)| key));
        self.admit_symbolic_numeric_work(&keys)
    }

    pub(in crate::eval) fn admit_symbolic_numeric_work(
        &self,
        values: &[&ModelValue],
    ) -> EvalResult<()> {
        if self.symbolic_active.borrow().is_empty() {
            return Ok(());
        }
        self.admit_evaluation(
            values.len(),
            values
                .len()
                .saturating_mul(std::mem::size_of::<(&ModelValue, usize)>()),
        )?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(values.len())
            .map_err(|_| "symbolic numeric admission allocation refused")?;
        pending.extend(values.iter().map(|&value| (value, 0usize)));
        let mut bits = 0usize;
        let mut nodes = 0usize;
        while let Some((value, depth)) = pending.pop() {
            nodes = nodes
                .checked_add(1)
                .ok_or("symbolic numeric work overflow")?;
            if nodes > 4096 || depth >= 64 {
                return Err("symbolic numeric operand exceeds bounded shape".into());
            }
            self.charge_sequence_work(1)?;
            let magnitude = match value {
                ModelValue::Bool(_) => 0,
                ModelValue::Int(value) => {
                    usize::try_from(value.bits()).map_err(|_| "symbolic integer size overflow")?
                }
                ModelValue::Real(value) => {
                    use num_traits::Signed;
                    if !value.denom().is_positive() {
                        return Err("symbolic rational has an invalid denominator".into());
                    }
                    value
                        .numer()
                        .bits()
                        .checked_add(value.denom().bits())
                        .and_then(|bits| usize::try_from(bits).ok())
                        .ok_or("symbolic rational size overflow")?
                }
                ModelValue::Array(array) => {
                    let count = array
                        .store
                        .len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(1))
                        .ok_or("symbolic array edge overflow")?;
                    let bytes = pending
                        .capacity()
                        .checked_add(pending.len())
                        .and_then(|n| n.checked_add(count))
                        .and_then(|n| n.checked_mul(std::mem::size_of::<(&ModelValue, usize)>()))
                        .ok_or("symbolic array storage overflow")?;
                    self.admit_evaluation(count, bytes)?;
                    self.charge_sequence_work(count)?;
                    pending
                        .try_reserve_exact(count)
                        .map_err(|_| "symbolic numeric array allocation refused")?;
                    pending.push((&array.default, depth + 1));
                    for (key, value) in &array.store {
                        pending.push((key, depth + 1));
                        pending.push((value, depth + 1));
                    }
                    0
                }
                _ => {
                    return Err(
                        "symbolic numeric operation has an unsupported value carrier".into(),
                    )
                }
            };
            bits = bits
                .checked_add(magnitude)
                .ok_or("symbolic numeric magnitude overflow")?;
        }
        // Sum of all input bits bounds intermediate numerator/denominator
        // growth of these finite folds. Cubic bit work conservatively includes
        // multiplication, division, GCD normalization and rational comparison;
        // no arithmetic or operand clone precedes this original-owner debit.
        let width = bits
            .checked_add(nodes)
            .and_then(|n| n.checked_add(1))
            .ok_or("symbolic numeric width overflow")?;
        let work = width
            .checked_mul(width)
            .and_then(|n| n.checked_mul(width))
            .and_then(|n| n.checked_mul(nodes.checked_add(1)?))
            .ok_or("symbolic numeric work overflow")?;
        let bytes = width
            .checked_mul(128)
            .ok_or("symbolic numeric storage overflow")?;
        self.admit_evaluation(work, bytes)?;
        self.charge_sequence_work(work)
    }
}
