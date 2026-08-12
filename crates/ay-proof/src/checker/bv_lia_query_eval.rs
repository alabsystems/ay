// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Application evaluation for the independently checked Bool/Int/BV query fragment.

use std::collections::HashMap;

use ay_core::{Symbol, TermId};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::integer_evaluation::integer_limb_units;
use super::{
    arithmetic_shift_right, bv_mask, signed_bv, BvLiaUnsatAuthenticationError, Environment,
    QueryChecker, Value,
};

impl QueryChecker<'_> {
    pub(super) fn eval_bool_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        let name = symbol.name();
        let bool_value = match name {
            "and" => {
                let mut unknown = false;
                for &arg in args {
                    match self.eval_bool(arg, env, memo, depth + 1)? {
                        Some(false) => return Ok(Some(Value::Bool(false))),
                        Some(true) => {}
                        None => unknown = true,
                    }
                }
                (!unknown).then_some(true)
            }
            "or" => {
                let mut unknown = false;
                for &arg in args {
                    match self.eval_bool(arg, env, memo, depth + 1)? {
                        Some(true) => return Ok(Some(Value::Bool(true))),
                        Some(false) => {}
                        None => unknown = true,
                    }
                }
                (!unknown).then_some(false)
            }
            "not" if args.len() == 1 => self
                .eval_bool(args[0], env, memo, depth + 1)?
                .map(|value| !value),
            "=>" | "implies" if args.len() == 2 => {
                match (
                    self.eval_bool(args[0], env, memo, depth + 1)?,
                    self.eval_bool(args[1], env, memo, depth + 1)?,
                ) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }
            "xor" if args.len() == 2 => self
                .eval_bool(args[0], env, memo, depth + 1)?
                .zip(self.eval_bool(args[1], env, memo, depth + 1)?)
                .map(|(left, right)| left ^ right),
            "=" if args.len() == 2 => self.eval_value_equality(args, env, memo, depth + 1)?,
            "distinct" if args.len() == 2 => self
                .eval_value_equality(args, env, memo, depth + 1)?
                .map(|equal| !equal),
            "<" | "<=" | ">" | ">=" if args.len() == 2 => {
                self.eval_int_relation(name, args, env, memo, depth + 1)?
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                if args.len() == 2 =>
            {
                self.eval_bv(args[0], env, memo, depth + 1)?
                    .zip(self.eval_bv(args[1], env, memo, depth + 1)?)
                    .and_then(|((left, left_width), (right, right_width))| {
                        (left_width == right_width).then(|| match name {
                            "bvult" => left < right,
                            "bvule" => left <= right,
                            "bvugt" => left > right,
                            "bvuge" => left >= right,
                            "bvslt" => signed_bv(left, left_width) < signed_bv(right, right_width),
                            "bvsle" => signed_bv(left, left_width) <= signed_bv(right, right_width),
                            "bvsgt" => signed_bv(left, left_width) > signed_bv(right, right_width),
                            "bvsge" => signed_bv(left, left_width) >= signed_bv(right, right_width),
                            _ => unreachable!(),
                        })
                    })
            }
            _ => None,
        };
        Ok(bool_value.map(Value::Bool))
    }

    fn eval_value_equality(
        &mut self,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<bool>, BvLiaUnsatAuthenticationError> {
        let left = self.eval_value(args[0], env, memo, depth + 1)?;
        let right = self.eval_value(args[1], env, memo, depth + 1)?;
        match (left, right) {
            (Some(left), Some(right)) => Ok(Some(self.values_equal(&left, &right)?)),
            _ => Ok(None),
        }
    }

    fn eval_int_relation(
        &mut self,
        name: &str,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<bool>, BvLiaUnsatAuthenticationError> {
        let left = self.eval_int(args[0], env, memo, depth + 1)?;
        let right = self.eval_int(args[1], env, memo, depth + 1)?;
        let Some((left, right)) = left.zip(right) else {
            return Ok(None);
        };
        self.meter
            .charge(integer_limb_units(&left).max(integer_limb_units(&right)))?;
        Ok(Some(match name {
            "<" => left < right,
            "<=" => left <= right,
            ">" => left > right,
            ">=" => left >= right,
            _ => return Ok(None),
        }))
    }

    pub(super) fn values_equal(
        &mut self,
        left: &Value,
        right: &Value,
    ) -> Result<bool, BvLiaUnsatAuthenticationError> {
        if let (Value::Int(left), Value::Int(right)) = (left, right) {
            self.meter
                .charge(integer_limb_units(left).max(integer_limb_units(right)))?;
        }
        Ok(left == right)
    }

    pub(super) fn eval_int_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        let name = symbol.name();
        let value = match name {
            "+" => {
                let mut value = BigInt::zero();
                for &arg in args {
                    let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    value = self.add_bounded_ints(&value, &arg)?;
                }
                Some(value)
            }
            "-" => match args {
                [] => None,
                [arg] => match self.eval_int(*arg, env, memo, depth + 1)? {
                    Some(value) => Some(self.negate_bounded_int(value)?),
                    None => None,
                },
                [first, rest @ ..] => {
                    let Some(mut value) = self.eval_int(*first, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    for &arg in rest {
                        let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                            return Ok(None);
                        };
                        value = self.subtract_bounded_ints(&value, &arg)?;
                    }
                    Some(value)
                }
            },
            "*" => {
                let mut value = BigInt::one();
                for &arg in args {
                    let Some(arg) = self.eval_int(arg, env, memo, depth + 1)? else {
                        return Ok(None);
                    };
                    value = self.multiply_bounded_ints(value, arg)?;
                }
                Some(value)
            }
            "mod" if args.len() == 2 => {
                let dividend = self.eval_int(args[0], env, memo, depth + 1)?;
                let divisor = self.eval_int(args[1], env, memo, depth + 1)?;
                match (dividend, divisor) {
                    (Some(dividend), Some(divisor)) if divisor.is_positive() => {
                        Some(self.modulo_bounded_ints(&dividend, &divisor)?)
                    }
                    _ => None,
                }
            }
            "abs" if args.len() == 1 => match self.eval_int(args[0], env, memo, depth + 1)? {
                Some(value) => Some(self.abs_bounded_int(value)?),
                None => None,
            },
            "bv2nat" if args.len() == 1 => self
                .eval_bv(args[0], env, memo, depth + 1)?
                .map(|(value, _)| BigInt::from(value)),
            _ => None,
        };
        Ok(value.map(Value::Int))
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn eval_bv_app(
        &mut self,
        symbol: &Symbol,
        args: &[TermId],
        expected_width: u32,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        if let Symbol::Indexed(name, indices) = symbol {
            return self.eval_indexed_bv_app(name, indices, args, expected_width, env, memo, depth);
        }
        self.eval_named_bv_app(symbol.name(), args, expected_width, env, memo, depth)
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_indexed_bv_app(
        &mut self,
        name: &str,
        indices: &[u32],
        args: &[TermId],
        expected_width: u32,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        if name == "int2bv" && indices == [expected_width] && args.len() == 1 {
            let value = self.eval_int(args[0], env, memo, depth + 1)?;
            let Some(value) = value else {
                return Ok(None);
            };
            return Ok(self
                .residue_bounded_int(&value, expected_width)?
                .map(|value| Value::BitVec {
                    value,
                    width: expected_width,
                }));
        }
        if args.len() == 1 {
            let Some((value, width)) = self.eval_bv(args[0], env, memo, depth + 1)? else {
                return Ok(None);
            };
            let result = match (name, indices) {
                ("extract", [high, low]) if high >= low && *high < width => {
                    Some((value >> low, high - low + 1))
                }
                ("zero_extend", [added]) if width.checked_add(*added) == Some(expected_width) => {
                    Some((value, expected_width))
                }
                ("sign_extend", [added]) if width.checked_add(*added) == Some(expected_width) => {
                    let signed = signed_bv(value, width);
                    Some((
                        (signed as u128 & u128::from(bv_mask(expected_width))) as u64,
                        expected_width,
                    ))
                }
                _ => None,
            };
            return Ok(result.map(|(value, width)| Value::BitVec {
                value: value & bv_mask(width),
                width,
            }));
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_named_bv_app(
        &mut self,
        name: &str,
        args: &[TermId],
        expected_width: u32,
        env: &Environment,
        memo: &mut HashMap<TermId, Value>,
        depth: usize,
    ) -> Result<Option<Value>, BvLiaUnsatAuthenticationError> {
        if matches!(name, "bvnot" | "bvneg") && args.len() == 1 {
            let value = self.eval_bv(args[0], env, memo, depth + 1)?;
            return Ok(value.map(|(value, width)| Value::BitVec {
                value: if name == "bvnot" {
                    !value & bv_mask(width)
                } else {
                    0_u64.wrapping_sub(value) & bv_mask(width)
                },
                width,
            }));
        }
        if args.len() != 2 {
            return Ok(None);
        }
        let Some((left, left_width)) = self.eval_bv(args[0], env, memo, depth + 1)? else {
            return Ok(None);
        };
        let Some((right, right_width)) = self.eval_bv(args[1], env, memo, depth + 1)? else {
            return Ok(None);
        };
        if name == "concat" {
            let Some(width) = left_width.checked_add(right_width) else {
                return Ok(None);
            };
            if width != expected_width || width > 64 {
                return Ok(None);
            }
            let value = if right_width == 64 {
                right
            } else {
                (left << right_width) | right
            };
            return Ok(Some(Value::BitVec {
                value: value & bv_mask(width),
                width,
            }));
        }
        if left_width != right_width || left_width != expected_width {
            return Ok(None);
        }
        let width = left_width;
        let mask = bv_mask(width);
        let value = match name {
            "bvadd" => left.wrapping_add(right) & mask,
            "bvsub" => left.wrapping_sub(right) & mask,
            "bvmul" => left.wrapping_mul(right) & mask,
            "bvand" => left & right,
            "bvor" => left | right,
            "bvxor" => left ^ right,
            "bvnand" => !(left & right) & mask,
            "bvnor" => !(left | right) & mask,
            "bvxnor" => !(left ^ right) & mask,
            "bvshl" => {
                if right >= u64::from(width) {
                    0
                } else {
                    left.wrapping_shl(right as u32) & mask
                }
            }
            "bvlshr" => {
                if right >= u64::from(width) {
                    0
                } else {
                    left >> right
                }
            }
            "bvashr" => arithmetic_shift_right(left, right, width),
            _ => return Ok(None),
        };
        Ok(Some(Value::BitVec { value, width }))
    }
}
