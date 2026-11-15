// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<E> Evaluator<'_, '_, E> {
    pub(super) fn indexed(
        &mut self,
        name: &str,
        indices: &[u32],
        args: &[TermId],
    ) -> EvalResult<EvalValue, E> {
        match name {
            "extract" if indices.len() == 2 && args.len() == 1 => {
                let (high, low) = (indices[0], indices[1]);
                let (value, source_width) = self.bitvector(args[0])?;
                if high < low || high >= source_width {
                    return Err(EvalError::Unsupported);
                }
                let width = high
                    .checked_sub(low)
                    .and_then(|width| width.checked_add(1))
                    .ok_or(EvalError::Unsupported)?;
                Ok(EvalValue::BitVec {
                    value: (value >> low) & bv_mask(width),
                    width,
                })
            }
            "zero_extend" if indices.len() == 1 && args.len() == 1 => {
                let (value, source_width) = self.bitvector(args[0])?;
                let width = source_width
                    .checked_add(indices[0])
                    .ok_or(EvalError::Unsupported)?;
                if width > MAX_EVALUATED_BV_WIDTH {
                    return Err(EvalError::Unsupported);
                }
                Ok(EvalValue::BitVec {
                    value: value & bv_mask(width),
                    width,
                })
            }
            "sign_extend" if indices.len() == 1 && args.len() == 1 => {
                let (value, source_width) = self.bitvector(args[0])?;
                let width = source_width
                    .checked_add(indices[0])
                    .ok_or(EvalError::Unsupported)?;
                if source_width == 0 || width > MAX_EVALUATED_BV_WIDTH {
                    return Err(EvalError::Unsupported);
                }
                let negative = source_width > 0 && (value >> (source_width - 1)) & 1 == 1;
                let value = if negative {
                    value | (bv_mask(width) ^ bv_mask(source_width))
                } else {
                    value
                };
                Ok(EvalValue::BitVec {
                    value: value & bv_mask(width),
                    width,
                })
            }
            "rotate_left" | "rotate_right" if indices.len() == 1 && args.len() == 1 => {
                let (value, width) = self.bitvector(args[0])?;
                let mask = bv_mask(width);
                let amount = indices[0] % width.max(1);
                let value = if amount == 0 {
                    value
                } else if name == "rotate_left" {
                    ((value << amount) | (value >> (width - amount))) & mask
                } else {
                    ((value >> amount) | (value << (width - amount))) & mask
                };
                Ok(EvalValue::BitVec { value, width })
            }
            "repeat" if indices.len() == 1 && args.len() == 1 => self.repeat(indices[0], args[0]),
            _ => Err(EvalError::Unsupported),
        }
    }

    fn repeat(&mut self, count: u32, arg: TermId) -> EvalResult<EvalValue, E> {
        if count == 0 {
            return Err(EvalError::Unsupported);
        }
        let (value, width) = self.bitvector(arg)?;
        let total = width.checked_mul(count).ok_or(EvalError::Unsupported)?;
        if width == 0 || total > MAX_EVALUATED_BV_WIDTH {
            return Err(EvalError::Unsupported);
        }
        let mut result = 0u64;
        for index in 0..count {
            self.poll()?;
            result = if index == 0 {
                value
            } else {
                (result << width) | value
            };
        }
        Ok(EvalValue::BitVec {
            value: result & bv_mask(total),
            width: total,
        })
    }
}
