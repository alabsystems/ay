// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Rust primitive NaN contract: sign arbitrary; quietness/payload retain raw provenance.
//! https://doc.rust-lang.org/std/primitive.f32.html#nan-bit-patterns

use super::construct::{checked, extract, fields};
use super::{FpAdapterError, RustNanPolicy};
use ay_bindings::Expr;

pub(super) fn permitted(
    word: &Expr,
    value: Expr,
    inputs: &[&Expr],
    width: u32,
    policy: RustNanPolicy,
) -> Result<Expr, FpAdapterError> {
    let fraction = if width == 32 { 23 } else { 52 };
    let quiet_bit = fraction - 1;
    let significand = extract(word, quiet_bit, 0)?;
    let payload = extract(word, quiet_bit - 1, 0)?;
    let quiet = checked(extract(word, quiet_bit, quiet_bit)?.try_eq(Expr::bitvec_const(1u8, 1)))?;
    let preferred = Expr::bitvec_const(1u64 << quiet_bit, fraction);
    let mut allowed = checked(significand.clone().try_eq(preferred.clone()))?;
    let mut nonpreferred_input = Expr::false_();
    for input in inputs {
        let nan = checked(fields(input, width)?.try_fp_is_nan())?;
        let input_significand = extract(input, quiet_bit, 0)?;
        let same_payload = checked(payload.clone().try_eq(extract(input, quiet_bit - 1, 0)?))?;
        let quieted = checked(quiet.clone().try_and(same_payload))?;
        let unchanged = checked(significand.clone().try_eq(input_significand.clone()))?;
        let propagated = checked(nan.clone().try_and(checked(quieted.try_or(unchanged))?))?;
        allowed = checked(allowed.try_or(propagated))?;
        let nonpreferred =
            checked(checked(input_significand.try_eq(preferred.clone()))?.try_not())?;
        nonpreferred_input =
            checked(nonpreferred_input.try_or(checked(nan.try_and(nonpreferred))?))?;
    }
    let extra = match policy {
        RustNanPolicy::NoExtra => Expr::false_(),
        RustNanPolicy::AllQuietPayloads => quiet,
        RustNanPolicy::AllOnesQuietPayload => {
            checked(significand.try_eq(Expr::bitvec_const((1u64 << fraction) - 1, fraction)))?
        }
        RustNanPolicy::WasmConditional => checked(quiet.try_and(nonpreferred_input))?,
    };
    let allowed = checked(allowed.try_or(extra))?;
    let non_nan = checked(checked(value.try_fp_is_nan())?.try_not())?;
    checked(non_nan.try_or(allowed))
}
