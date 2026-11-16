// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact typed IEEE field extraction, before any fixed-width conversion.

use super::*;

#[cfg(test)]
mod tests;

impl Executor {
    fn fp_field_bits(&self, model: &Model, term: TermId, width: u32) -> Option<BigInt> {
        self.ctx.terms.entry_stamp(term)?;
        let Sort::BitVec(declared) = self.ctx.terms.sort(term) else {
            return None;
        };
        if declared.width != width {
            return None;
        }
        let EvalValue::BitVec {
            value,
            width: actual,
        } = self.evaluate_term(model, term)
        else {
            return None;
        };
        if actual != width
            || value.is_negative()
            || value.bits() > u64::from(width)
            || self.evaluation_stop_origin().is_some()
        {
            return None;
        }
        Some(value)
    }

    pub(super) fn fp_from_model_fields(
        &self,
        model: &Model,
        args: &[TermId],
        sort: &Sort,
    ) -> Option<FpModelValue> {
        let (&Sort::FloatingPoint(eb, sb), &[sign, exponent, significand]) = (sort, args) else {
            return None;
        };
        // Use the checked carrier's format admission before computing sb-1 or
        // evaluating any operand. No solve-format admission is granted here.
        if eb < 2 || sb < 2 || eb.checked_add(sb).is_none() {
            return None;
        }
        let sign = self.fp_field_bits(model, sign, 1)?.to_u8()? == 1;
        let exponent = self.fp_field_bits(model, exponent, eb)?.to_biguint()?;
        let significand = self
            .fp_field_bits(model, significand, sb - 1)?
            .to_biguint()?;
        FpModelValue::from_exact_fields(sign, exponent, significand, eb, sb)
    }

    pub(super) fn fp_from_model_ieee_bits(
        &self,
        model: &Model,
        term: TermId,
        sort: &Sort,
    ) -> Option<FpModelValue> {
        let &Sort::FloatingPoint(eb, sb) = sort else {
            return None;
        };
        if eb < 2 || sb < 2 || eb.checked_add(sb).is_none() {
            return None;
        }
        let value = self.fp_field_bits(model, term, eb.checked_add(sb)?)?;
        FpModelValue::from_ieee_bv(&value, eb, sb)
    }
}
