// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB 2.6 §3.1 binary and hexadecimal invariant literals.
//! Width is authenticated before integer or literal-tree allocation.

use super::InvariantParser;
use crate::{ChcError, ChcExpr, ChcResult, MAX_BITVECTOR_WIDTH};

impl InvariantParser<'_> {
    pub(super) fn parse_radix_literal(&mut self) -> ChcResult<ChcExpr> {
        let bytes = self.input.as_bytes();
        if bytes.get(self.pos) != Some(&b'#') {
            return Err(ChcError::Parse("Expected bitvector literal prefix".into()));
        }
        self.pos += 1;
        let (radix, bits_per_digit) = match bytes.get(self.pos) {
            Some(b'b') => (2, 1_u32),
            Some(b'x') => (16, 4_u32),
            _ => {
                return Err(ChcError::Parse(
                    "Expected lowercase #b or #x bitvector literal".into(),
                ));
            }
        };
        self.pos += 1;
        let start = self.pos;
        let mut width = 0_u32;
        while let Some(&byte) = bytes.get(self.pos) {
            if matches!(byte, b' ' | b'\t' | b'\r' | b'\n' | b';' | b'(' | b')') {
                break;
            }
            if !(if radix == 2 {
                matches!(byte, b'0' | b'1')
            } else {
                byte.is_ascii_hexdigit()
            }) {
                return Err(ChcError::Parse(
                    "Invalid digit or suffix in bitvector literal".into(),
                ));
            }
            width = width
                .checked_add(bits_per_digit)
                .filter(|width| *width <= MAX_BITVECTOR_WIDTH)
                .ok_or_else(|| {
                    ChcError::Parse(format!(
                        "bitvector literal width exceeds the supported maximum {MAX_BITVECTOR_WIDTH}"
                    ))
                })?;
            self.pos += 1;
        }
        if width == 0 {
            return Err(ChcError::Parse("Empty bitvector literal".into()));
        }
        // Every consumed byte is ASCII, so these are UTF-8 boundaries. The
        // complete token is validated: #b01bad cannot become a short literal
        // followed by an unrelated free Int variable.
        let digits = &self.input[start..self.pos];
        if width <= 128 {
            let value = u128::from_str_radix(digits, radix)
                .map_err(|_| ChcError::Parse("Invalid compact bitvector literal".into()))?;
            return Ok(ChcExpr::BitVec(value, width));
        }
        // This is the same exact, bounded concat carrier as indexed decimal
        // literals, not an additional BigBitVec representation or modulo
        // acceptance of an overwide value.
        let value = num_bigint::BigUint::parse_bytes(digits.as_bytes(), radix)
            .ok_or_else(|| ChcError::Parse("Invalid wide bitvector literal".into()))?;
        if value.bits() > u64::from(width) {
            return Err(ChcError::Parse(
                "Bitvector literal value does not fit its derived width".into(),
            ));
        }
        ChcExpr::bitvec_from_biguint(&value, width)
    }
}

#[cfg(test)]
mod tests;
