// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<E> Evaluator<'_, '_, E> {
    pub(super) fn app(&mut self, symbol: &Symbol, args: &[TermId]) -> EvalResult<EvalValue, E> {
        if let Symbol::Indexed(name, indices) = symbol {
            return self.indexed(name, indices, args);
        }
        let name = symbol.name();
        match name {
            "=" if args.len() == 2 => {
                Ok(EvalValue::Bool(self.term(args[0])? == self.term(args[1])?))
            }
            "or" | "and" => {
                let mut value = name == "and";
                for &arg in args {
                    self.poll()?;
                    // Preserve evaluation of ALL children, even after true
                    // for or / false for and: unsupported children still fail.
                    let child = self.boolean(arg)?;
                    if name == "or" {
                        value |= child;
                    } else {
                        value &= child;
                    }
                }
                Ok(EvalValue::Bool(value))
            }
            "bvnot" | "bvneg" if args.len() == 1 => {
                let (value, width) = self.bitvector(args[0])?;
                let value = if name == "bvnot" {
                    !value
                } else {
                    value.wrapping_neg()
                };
                Ok(EvalValue::BitVec {
                    value: value & bv_mask(width),
                    width,
                })
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                if args.len() == 2 =>
            {
                self.compare(name, args)
            }
            "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvadd" | "bvsub"
            | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod" | "bvshl"
            | "bvlshr" | "bvashr"
                if args.len() == 2 =>
            {
                self.binary(name, args)
            }
            "concat" if args.len() == 2 => {
                let (high, high_width) = self.bitvector(args[0])?;
                let (low, low_width) = self.bitvector(args[1])?;
                let width = high_width
                    .checked_add(low_width)
                    .ok_or(EvalError::Unsupported)?;
                if high_width == 0 || low_width == 0 || width > MAX_EVALUATED_BV_WIDTH {
                    return Err(EvalError::Unsupported);
                }
                Ok(EvalValue::BitVec {
                    value: ((high << low_width) | low) & bv_mask(width),
                    width,
                })
            }
            _ => Err(EvalError::Unsupported),
        }
    }

    fn compare(&mut self, name: &str, args: &[TermId]) -> EvalResult<EvalValue, E> {
        let (left, right, width) = self.same_width(args)?;
        let (signed_left, signed_right) = (to_signed_u64(left, width), to_signed_u64(right, width));
        let value = match name {
            "bvult" => left < right,
            "bvule" => left <= right,
            "bvugt" => left > right,
            "bvuge" => left >= right,
            "bvslt" => signed_left < signed_right,
            "bvsle" => signed_left <= signed_right,
            "bvsgt" => signed_left > signed_right,
            "bvsge" => signed_left >= signed_right,
            _ => unreachable!("guarded by match arm"),
        };
        Ok(EvalValue::Bool(value))
    }

    fn binary(&mut self, name: &str, args: &[TermId]) -> EvalResult<EvalValue, E> {
        let (left, right, width) = self.same_width(args)?;
        let value = match name {
            "bvand" => left & right,
            "bvor" => left | right,
            "bvxor" => left ^ right,
            "bvnand" => !(left & right),
            "bvnor" => !(left | right),
            "bvxnor" => !(left ^ right),
            "bvadd" => left.wrapping_add(right),
            "bvsub" => left.wrapping_sub(right),
            "bvmul" => left.wrapping_mul(right),
            "bvudiv" => left.checked_div(right).unwrap_or_else(|| bv_mask(width)),
            "bvurem" => left.checked_rem(right).unwrap_or(left),
            "bvsdiv" | "bvsrem" | "bvsmod" => eval_bv_signed_divrem(name, left, right, width),
            "bvshl" | "bvlshr" | "bvashr" => eval_bv_shift(name, left, right, width),
            _ => unreachable!("guarded by match arm"),
        } & bv_mask(width);
        Ok(EvalValue::BitVec { value, width })
    }
}
