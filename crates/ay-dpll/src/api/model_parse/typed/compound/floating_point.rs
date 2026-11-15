// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::types::FpSpecialKind;

impl Decoder<'_> {
    pub(in super::super) fn floating_point(
        &mut self,
        value: &SExpr,
        eb: u32,
        sb: u32,
    ) -> Option<ModelValue> {
        self.charge(1)?;
        if eb < 2 || sb < 2 {
            return None;
        }
        let values = value.as_list()?;
        match values {
            [head, kind, exponent, significand] if head.is_symbol("_") => {
                if sorts::numeral(exponent)? != eb || sorts::numeral(significand)? != sb {
                    return None;
                }
                let kind = match kind.as_symbol()? {
                    "+zero" => FpSpecialKind::PosZero,
                    "-zero" => FpSpecialKind::NegZero,
                    "+oo" => FpSpecialKind::PosInf,
                    "-oo" => FpSpecialKind::NegInf,
                    "NaN" => FpSpecialKind::NaN,
                    _ => return None,
                };
                Some(ModelValue::FloatingPointSpecial { kind, eb, sb })
            }
            [head, sign, exponent, significand] if head.is_symbol("fp") => {
                // Reuse the same bounded bitvector decoder for all three
                // fields, including standard indexed decimal BV literals.
                // It pays actual digits/copies, not an unoccupied declared width.
                let mut bits = |value, width| {
                    let ModelValue::BitVec { value, .. } = self.bitvector(value, width)? else {
                        return None;
                    };
                    value.to_biguint()
                };
                ModelValue::from_fp_exact_fields(
                    bits(sign, 1)?.bit(0),
                    bits(exponent, eb)?,
                    bits(significand, sb - 1)?,
                    eb,
                    sb,
                )
            }
            _ => None,
        }
    }
}
