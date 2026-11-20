// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent interpretation of linear model DATA at the gate's own point.
//! This module never calls the native model evaluator or LinearIntBody::evaluate.

use super::ModelValue;
use crate::executor::model::certificate_data::LinearIntBody;
use num_bigint::BigInt;

fn words(value: &BigInt) -> Result<usize, ()> {
    // Count at least as many 32-bit digits as either supported BigInt limb
    // representation needs. Schoolbook digit products conservatively bound
    // the multiplication work; temporary products/sums are paid before use.
    usize::try_from(value.bits().div_ceil(32))
        .map(|words| words.max(1))
        .map_err(|_| ())
}

pub(super) fn evaluate(
    body: &LinearIntBody,
    arguments: &[ModelValue],
    admit: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<BigInt, ()> {
    if arguments.len() != body.arity() {
        return Err(());
    }
    // Opposite fold order and an independently applied intercept. Exact
    // integer arithmetic has no overflow or order-dependent rounding.
    let mut sum = BigInt::from(0);
    for (coefficient, argument) in body.coefficients().iter().zip(arguments).rev() {
        let ModelValue::Int(argument) = argument else {
            return Err(());
        };
        let (a, b, s) = (words(coefficient)?, words(argument)?, words(&sum)?);
        let work = a
            .checked_mul(b)
            .and_then(|n| n.checked_add(a))
            .and_then(|n| n.checked_add(b))
            .and_then(|n| n.checked_add(s))
            .and_then(|n| n.checked_add(1))
            .ok_or(())?;
        let bytes = a
            .checked_add(b)
            .and_then(|n| n.checked_add(s))
            .and_then(|n| n.checked_add(4))
            .and_then(|n| n.checked_mul(4 * std::mem::size_of::<usize>()))
            .ok_or(())?;
        if !admit(work, bytes) {
            return Err(());
        }
        sum = coefficient * argument + sum;
    }
    let work = words(body.constant())?
        .checked_add(words(&sum)?)
        .and_then(|n| n.checked_add(1))
        .ok_or(())?;
    let bytes = work
        .checked_add(2)
        .and_then(|n| n.checked_mul(4 * std::mem::size_of::<usize>()))
        .ok_or(())?;
    if !admit(work, bytes) {
        return Err(());
    }
    let value = sum + body.constant();
    admit(0, 0).then_some(value).ok_or(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_gate_rederives_signed_positional_and_arbitrary_precision_values() {
        let body = LinearIntBody::new(vec![3.into(), (-2).into(), 0.into()], 7.into()).unwrap();
        let point = [
            ModelValue::Int((-5).into()),
            ModelValue::Int(4.into()),
            ModelValue::Int(123.into()),
        ];
        assert_eq!(evaluate(&body, &point, &mut |_, _| true), Ok((-16).into()));
        let large = BigInt::from(1) << 140usize;
        let body = LinearIntBody::new(vec![large.clone()], (-1).into()).unwrap();
        assert_eq!(
            evaluate(&body, &[ModelValue::Int(3.into())], &mut |_, _| true),
            Ok(3 * large - 1)
        );
    }

    #[test]
    fn linear_gate_refuses_wrong_arity_and_noninteger_even_at_zero_coefficient() {
        let body = LinearIntBody::new(vec![0.into(), 1.into()], 0.into()).unwrap();
        for point in [
            vec![],
            vec![ModelValue::Int(1.into())],
            vec![ModelValue::Bool(false), ModelValue::Int(1.into())],
        ] {
            assert!(evaluate(&body, &point, &mut |_, _| true).is_err());
        }
    }

    #[test]
    fn linear_gate_original_admission_can_refuse_each_arithmetic_or_cleanup_step() {
        let body = LinearIntBody::new(vec![2.into(), (-3).into()], 9.into()).unwrap();
        let point = [ModelValue::Int(4.into()), ModelValue::Int(5.into())];
        let mut calls = 0;
        let mut paid = 0;
        assert_eq!(
            evaluate(&body, &point, &mut |work, bytes| {
                calls += 1;
                paid += bytes;
                assert!(work > 0 || bytes == 0);
                true
            }),
            Ok(2.into())
        );
        assert!(paid > 0);
        for stop in 0..calls {
            let mut current = 0;
            assert!(evaluate(&body, &point, &mut |_, _| {
                let accepted = current != stop;
                current += 1;
                accepted
            })
            .is_err());
        }
    }
}
