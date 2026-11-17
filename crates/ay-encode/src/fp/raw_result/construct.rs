// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{FpAdapterError, FpRawOperation, FpRawResultRelation, RustFpArithmetic};
use ay_bindings::{Expr, RoundingMode};

pub(super) fn checked<T>(value: Result<T, ay_bindings::SortError>) -> Result<T, FpAdapterError> {
    value.map_err(|_| FpAdapterError::Invalid("raw-result constructor sort"))
}

pub(super) fn extract(word: &Expr, high: u32, low: u32) -> Result<Expr, FpAdapterError> {
    checked(word.clone().try_extract(high, low))
}

pub(super) fn fields(word: &Expr, width: u32) -> Result<Expr, FpAdapterError> {
    let fraction = if width == 32 { 23 } else { 52 };
    checked(Expr::try_fp_from_bvs(
        extract(word, width - 1, width - 1)?,
        extract(word, width - 2, fraction)?,
        extract(word, fraction - 1, 0)?,
    ))
}

pub(super) fn relation(
    result: &FpRawResultRelation<'_>,
    width: u32,
) -> Result<Expr, FpAdapterError> {
    match result.operation {
        FpRawOperation::Copy(input) => checked(input.clone().try_eq(result.output.clone())),
        FpRawOperation::Negate(input) | FpRawOperation::AbsoluteValue(input) => {
            let low = checked(extract(input, width - 2, 0)?.try_eq(extract(
                result.output,
                width - 2,
                0,
            )?))?;
            let sign = extract(result.output, width - 1, width - 1)?;
            let sign = match result.operation {
                FpRawOperation::Negate(_) => {
                    checked(checked(sign.try_eq(extract(input, width - 1, width - 1)?))?.try_not())?
                }
                _ => checked(sign.try_eq(Expr::bitvec_const(0u8, 1)))?,
            };
            checked(low.try_and(sign))
        }
        FpRawOperation::SignedIntegerToFpRne(input)
        | FpRawOperation::UnsignedIntegerToFpRne(input) => {
            let (e, s) = if width == 32 { (8, 24) } else { (11, 53) };
            let value = match result.operation {
                FpRawOperation::SignedIntegerToFpRne(_) => {
                    checked(input.clone().try_bv_to_fp(RoundingMode::RNE, e, s))?
                }
                _ => checked(input.clone().try_bv_to_fp_unsigned(RoundingMode::RNE, e, s))?,
            };
            // Structural FP equality fixes every finite output bit, including +0.
            // All BV8..64 values are finite in both supported output formats.
            checked(value.try_eq(fields(result.output, width)?))
        }
        FpRawOperation::Arithmetic {
            operation,
            inputs,
            nan_policy,
        } => {
            let value = arithmetic(operation, inputs, width)?;
            let output = fields(result.output, width)?;
            let equality = checked(value.try_eq(output.clone()))?;
            let nan = super::nan::permitted(result.output, output, inputs, width, nan_policy)?;
            checked(equality.try_and(nan))
        }
    }
}

fn arithmetic(
    operation: RustFpArithmetic,
    inputs: &[&Expr],
    width: u32,
) -> Result<Expr, FpAdapterError> {
    let a = fields(inputs[0], width)?;
    let mode = RoundingMode::RNE;
    use RustFpArithmetic::{
        Add, Divide, FusedMultiplyAdd, Multiply, SquareRoot, Subtract, TruncatingRemainder,
    };
    match operation {
        SquareRoot => checked(a.try_fp_sqrt(mode)),
        FusedMultiplyAdd => {
            checked(a.try_fp_fma(mode, fields(inputs[1], width)?, fields(inputs[2], width)?))
        }
        Add => checked(a.try_fp_add(mode, fields(inputs[1], width)?)),
        Subtract => checked(a.try_fp_sub(mode, fields(inputs[1], width)?)),
        Multiply => checked(a.try_fp_mul(mode, fields(inputs[1], width)?)),
        Divide => checked(a.try_fp_div(mode, fields(inputs[1], width)?)),
        TruncatingRemainder => checked(a.try_fp_truncating_rem(fields(inputs[1], width)?)),
    }
}
