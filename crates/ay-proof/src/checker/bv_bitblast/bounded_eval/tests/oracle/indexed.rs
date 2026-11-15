// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn eval_indexed_bv(
    terms: &TermStore,
    name: &str,
    indices: &[u32],
    args: &[TermId],
    env: &[(TermId, EvalValue)],
) -> Option<EvalValue> {
    match name {
        "extract" if indices.len() == 2 && args.len() == 1 => {
            let (high, low) = (indices[0], indices[1]);
            let (value, src_width) = eval_bv_arg(terms, args[0], env)?;
            if high < low || high >= src_width {
                return None;
            }
            let width = high.checked_sub(low)?.checked_add(1)?;
            Some(EvalValue::BitVec {
                value: (value >> low) & bv_mask(width),
                width,
            })
        }
        "zero_extend" if indices.len() == 1 && args.len() == 1 => {
            let (value, src_width) = eval_bv_arg(terms, args[0], env)?;
            let width = src_width.checked_add(indices[0])?;
            if width > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            // The added high bits are zero; `value` is already masked to src_width.
            Some(EvalValue::BitVec {
                value: value & bv_mask(width),
                width,
            })
        }
        "sign_extend" if indices.len() == 1 && args.len() == 1 => {
            let (value, src_width) = eval_bv_arg(terms, args[0], env)?;
            let width = src_width.checked_add(indices[0])?;
            if src_width == 0 || width > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            let negative = src_width > 0 && (value >> (src_width - 1)) & 1 == 1;
            let extended = if negative {
                // Fill the added high bits with the sign bit (1).
                value | (bv_mask(width) ^ bv_mask(src_width))
            } else {
                value
            };
            Some(EvalValue::BitVec {
                value: extended & bv_mask(width),
                width,
            })
        }
        "rotate_left" | "rotate_right" if indices.len() == 1 && args.len() == 1 => {
            let (value, width) = eval_bv_arg(terms, args[0], env)?;
            let mask = bv_mask(width);
            let k = indices[0] % width.max(1);
            let rotated = if k == 0 {
                value
            } else if name == "rotate_left" {
                ((value << k) | (value >> (width - k))) & mask
            } else {
                ((value >> k) | (value << (width - k))) & mask
            };
            Some(EvalValue::BitVec {
                value: rotated,
                width,
            })
        }
        "repeat" if indices.len() == 1 && args.len() == 1 => {
            let count = indices[0];
            if count == 0 {
                return None; // (_ repeat 0) is not well-formed
            }
            let (value, width) = eval_bv_arg(terms, args[0], env)?;
            let total = width.checked_mul(count)?;
            if width == 0 || total > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            let mut result = 0u64;
            for index in 0..count {
                result = if index == 0 {
                    value
                } else {
                    (result << width) | value
                };
            }
            Some(EvalValue::BitVec {
                value: result & bv_mask(total),
                width: total,
            })
        }
        _ => None,
    }
}
