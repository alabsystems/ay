// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::ChcParser;
use crate::{ChcError, ChcExpr, ChcOp, ChcResult, ChcSort};
use std::sync::Arc;

impl ChcParser {
    /// Parse `(_ extract hi lo)` index arguments with hi >= lo validation.
    pub(super) fn parse_extract_indices(idx_args: &[String]) -> ChcResult<ChcExpr> {
        if idx_args.len() != 2 {
            return Err(ChcError::Parse(
                "(_ extract hi lo) requires exactly 2 index arguments".into(),
            ));
        }
        let hi: u32 = idx_args[0]
            .parse()
            .map_err(|_| ChcError::Parse(format!("Invalid extract high index: {}", idx_args[0])))?;
        let lo: u32 = idx_args[1]
            .parse()
            .map_err(|_| ChcError::Parse(format!("Invalid extract low index: {}", idx_args[1])))?;
        if hi < lo {
            return Err(ChcError::Parse(format!("extract: hi ({hi}) < lo ({lo})")));
        }
        Ok(ChcExpr::Op(ChcOp::BvExtract(hi, lo), vec![]))
    }

    /// Parse indexed expression like `(_ bv123 32)` or indexed BV ops like `(_ extract 7 0)`.
    ///
    /// Indexed BV ops return `ChcExpr::Op(indexed_op, vec![])` with zero args — the
    /// caller (`parse_higher_order_application`) fills in the actual arguments.
    pub(super) fn parse_indexed_expr(&mut self) -> ChcResult<ChcExpr> {
        self.expect_char('_')?;
        self.skip_whitespace_and_comments();

        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        let mut idx_args = Vec::new();
        while self.peek_char() != Some(')') {
            idx_args.push(self.parse_symbol()?);
            self.skip_whitespace_and_comments();
        }
        self.expect_char(')')?;

        match name.as_str() {
            _ if name.starts_with("bv") && name[2..].chars().all(|c| c.is_ascii_digit()) => {
                let width: u32 = idx_args
                    .first()
                    .ok_or_else(|| ChcError::Parse("Missing bitvector width".into()))?
                    .parse()
                    .map_err(|_| ChcError::Parse("Invalid bitvector width".into()))?;
                // Bound the width before encode_wide_decimal_bv's ~width/128
                // chunk loop (and make_all_ones_bv recursion) allocate from it.
                if width == 0 || width > super::sorts::MAX_BV_WIDTH {
                    return Err(ChcError::Parse(format!(
                        "bitvector width {width} is outside the supported range 1..={}",
                        super::sorts::MAX_BV_WIDTH
                    )));
                }
                if let Ok(value) = name[2..].parse::<u128>() {
                    Ok(ChcExpr::BitVec(value, width))
                } else {
                    Self::encode_wide_decimal_bv(&name[2..], width)
                }
            }
            "extract" => Self::parse_extract_indices(&idx_args),
            "zero_extend" | "sign_extend" | "rotate_left" | "rotate_right" | "repeat"
            | "int2bv" => {
                if idx_args.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "(_ {name} n) requires exactly 1 index argument"
                    )));
                }
                let n: u32 = idx_args[0].parse().map_err(|_| {
                    ChcError::Parse(format!("Invalid index for {name}: {}", idx_args[0]))
                })?;
                let op = match name.as_str() {
                    "zero_extend" => ChcOp::BvZeroExtend(n),
                    "sign_extend" => ChcOp::BvSignExtend(n),
                    "rotate_left" => ChcOp::BvRotateLeft(n),
                    "rotate_right" => ChcOp::BvRotateRight(n),
                    "repeat" => ChcOp::BvRepeat(n),
                    "int2bv" => ChcOp::Int2Bv(n),
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "Unexpected indexed operator: {name}"
                        )));
                    }
                };
                Ok(ChcExpr::Op(op, vec![]))
            }
            "is" => {
                if idx_args.len() != 1 {
                    return Err(ChcError::Parse(
                        "(_ is ...) requires exactly 1 argument".into(),
                    ));
                }
                Ok(ChcExpr::IsTesterMarker(
                    idx_args
                        .into_iter()
                        .next()
                        .expect("invariant: length checked above"),
                ))
            }
            _ => Err(ChcError::Parse(format!(
                "Unknown indexed identifier: {name}"
            ))),
        }
    }

    /// Parse a bitvector literal: `#xABCD` (hex) or `#b0101` (binary).
    ///
    /// SMT-LIB 2.6 §3.1:
    /// - `#xN` where N is a non-empty sequence of hex digits → BitVec of width 4*len(N)
    /// - `#bN` where N is a non-empty sequence of 0/1 → BitVec of width len(N)
    ///
    /// For BV > 128 bits (#7040), decomposes into BvConcat of ≤128-bit chunks.
    pub(super) fn parse_bv_literal(&mut self) -> ChcResult<ChcExpr> {
        assert_eq!(self.peek_char(), Some('#'));
        self.pos += 1;

        match self.peek_char() {
            Some('x') => {
                self.pos += 1;
                let start = self.pos;
                while self.pos < self.input.len() {
                    match self.current_char() {
                        Some(c) if c.is_ascii_hexdigit() => self.pos += 1,
                        _ => break,
                    }
                }
                let hex_str = &self.input[start..self.pos];
                if hex_str.is_empty() {
                    return Err(ChcError::Parse("Empty hex bitvector literal #x".into()));
                }
                let width = (hex_str.len() * 4) as u32;
                if width <= 128 {
                    let value = u128::from_str_radix(hex_str, 16).map_err(|e| {
                        ChcError::Parse(format!("Invalid hex bitvector literal #x{hex_str}: {e}"))
                    })?;
                    Ok(ChcExpr::BitVec(value, width))
                } else {
                    Ok(Self::encode_wide_hex_bv(hex_str, width))
                }
            }
            Some('b') => {
                self.pos += 1;
                let start = self.pos;
                while self.pos < self.input.len() {
                    match self.current_char() {
                        Some('0' | '1') => self.pos += 1,
                        _ => break,
                    }
                }
                let bin_str = &self.input[start..self.pos];
                if bin_str.is_empty() {
                    return Err(ChcError::Parse("Empty binary bitvector literal #b".into()));
                }
                let width = bin_str.len() as u32;
                if width <= 128 {
                    let value = u128::from_str_radix(bin_str, 2).map_err(|e| {
                        ChcError::Parse(format!(
                            "Invalid binary bitvector literal #b{bin_str}: {e}"
                        ))
                    })?;
                    Ok(ChcExpr::BitVec(value, width))
                } else {
                    Ok(Self::encode_wide_bin_bv(bin_str, width))
                }
            }
            Some(c) => Err(ChcError::Parse(format!(
                "Expected 'x' or 'b' after '#', got '{c}'"
            ))),
            None => Err(ChcError::Parse("Unexpected end of input after '#'".into())),
        }
    }

    /// Build an all-ones bitvector expression of the given width.
    /// For width <= 128, returns a single BitVec node.
    /// For width > 128, returns a BvConcat tree of 128-bit chunks.
    pub(super) fn make_all_ones_bv(width: u32) -> ChcExpr {
        if width <= 128 {
            let mask = if width == 128 {
                u128::MAX
            } else {
                (1u128 << width) - 1
            };
            ChcExpr::BitVec(mask, width)
        } else {
            let low_width = 128u32;
            let high_width = width - low_width;
            let low = ChcExpr::BitVec(u128::MAX, low_width);
            let high = Self::make_all_ones_bv(high_width);
            ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(high), Arc::new(low)])
        }
    }

    /// Encode a wide hex BV literal (>128 bits) as a BvConcat tree of ≤128-bit chunks.
    /// Processes from high bits to low bits (left to right in the hex string).
    pub(super) fn encode_wide_hex_bv(hex_str: &str, total_width: u32) -> ChcExpr {
        let mut chunks: Vec<(u128, u32)> = Vec::new();
        let mut remaining = hex_str;
        while !remaining.is_empty() {
            let chunk_len = remaining.len().min(32);
            let split_point = remaining.len() - chunk_len;
            let chunk_str = &remaining[split_point..];
            remaining = &remaining[..split_point];
            let chunk_width = (chunk_len * 4) as u32;
            let value = u128::from_str_radix(chunk_str, 16).unwrap_or(0);
            chunks.push((value, chunk_width));
        }
        chunks.reverse();
        let sum_width: u32 = chunks.iter().map(|(_, w)| *w).sum();
        debug_assert_eq!(sum_width, total_width);
        let last = chunks
            .last()
            .expect("invariant: hex string non-empty produces ≥1 chunk");
        let mut result = ChcExpr::BitVec(last.0, last.1);
        for &(value, width) in chunks.iter().rev().skip(1) {
            let chunk = ChcExpr::BitVec(value, width);
            result = ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(chunk), Arc::new(result)]);
        }
        result
    }

    /// Encode a wide binary BV literal (>128 bits) as a BvConcat tree.
    pub(super) fn encode_wide_bin_bv(bin_str: &str, total_width: u32) -> ChcExpr {
        let mut chunks: Vec<(u128, u32)> = Vec::new();
        let mut remaining = bin_str;
        while !remaining.is_empty() {
            let chunk_len = remaining.len().min(128);
            let split_point = remaining.len() - chunk_len;
            let chunk_str = &remaining[split_point..];
            remaining = &remaining[..split_point];
            let chunk_width = chunk_len as u32;
            let value = u128::from_str_radix(chunk_str, 2).unwrap_or(0);
            chunks.push((value, chunk_width));
        }
        chunks.reverse();
        let sum_width: u32 = chunks.iter().map(|(_, w)| *w).sum();
        debug_assert_eq!(sum_width, total_width);
        let last = chunks
            .last()
            .expect("invariant: bin string non-empty produces ≥1 chunk");
        let mut result = ChcExpr::BitVec(last.0, last.1);
        for &(value, width) in chunks.iter().rev().skip(1) {
            let chunk = ChcExpr::BitVec(value, width);
            result = ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(chunk), Arc::new(result)]);
        }
        result
    }

    /// Encode a wide decimal BV literal (>128 bits) as a BvConcat tree (#7040).
    ///
    /// Handles `(_ bvN W)` where N is a decimal integer exceeding u128::MAX.
    /// Parses N via BigUint, extracts ≤128-bit chunks from low to high, and
    /// builds a BvConcat tree matching the declared width.
    pub(super) fn encode_wide_decimal_bv(
        decimal_str: &str,
        total_width: u32,
    ) -> ChcResult<ChcExpr> {
        use num_bigint::BigUint;

        let big_val: BigUint = decimal_str.parse().map_err(|_| {
            ChcError::Parse(format!(
                "Invalid wide bitvector decimal literal: {decimal_str}"
            ))
        })?;

        let mask_128 = BigUint::from(u128::MAX);
        let mut remaining = big_val;
        let mut chunks: Vec<(u128, u32)> = Vec::new();
        let mut bits_left = total_width;

        while bits_left > 0 {
            let chunk_width = bits_left.min(128);
            let chunk_mask = if chunk_width == 128 {
                mask_128.clone()
            } else {
                (BigUint::from(1u128) << chunk_width as usize) - BigUint::from(1u128)
            };
            let chunk_val: u128 = (&remaining & &chunk_mask).try_into().unwrap_or(0);
            chunks.push((chunk_val, chunk_width));
            remaining >>= chunk_width as usize;
            bits_left -= chunk_width;
        }

        chunks.reverse();

        if chunks.is_empty() {
            return Ok(ChcExpr::BitVec(0, total_width));
        }

        let last = chunks
            .last()
            .expect("invariant: non-zero width produces ≥1 chunk");
        let mut result = ChcExpr::BitVec(last.0, last.1);
        for &(value, width) in chunks.iter().rev().skip(1) {
            let chunk = ChcExpr::BitVec(value, width);
            result = ChcExpr::Op(ChcOp::BvConcat, vec![Arc::new(chunk), Arc::new(result)]);
        }
        Ok(result)
    }
}

/// Infer BV width from a ChcExpr (for desugaring Z3-specific safe-division operators).
pub(super) fn infer_bv_width_from_expr(expr: &ChcExpr) -> Option<u32> {
    match expr {
        ChcExpr::BitVec(_, width) => Some(*width),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::BitVec(w) => Some(*w),
            _ => None,
        },
        ChcExpr::Op(_, args) => args.iter().find_map(|a| infer_bv_width_from_expr(a)),
        _ => None,
    }
}
