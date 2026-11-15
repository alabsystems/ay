// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl BvSolver<'_> {
    pub(crate) fn counted_bv_ite(
        &mut self,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
    ) -> BvBits {
        if !memory::set(&mut self.bv_ite_conditions, &self.encoding) {
            return Vec::new();
        }
        self.bv_ite_conditions.insert(cond);
        let selector = self.bitblast_bool(cond);
        let then_bits = self.get_bits(then_term);
        let else_bits = self.get_bits(else_term);
        if !self.encoding_complete() {
            return Vec::new();
        }
        self.bitwise_mux(&then_bits, &else_bits, selector)
    }

    pub(crate) fn counted_concat(&mut self, term: TermId) -> BvBits {
        let TermData::App(_, args) = self.terms.get(term) else {
            return Vec::new();
        };
        let [high, low] = args.as_slice() else {
            return Vec::new();
        };
        let high = *high;
        let low = *low;
        let low_bits = self.get_bits(low);
        let high_bits = self.get_bits(high);
        let Some(width) = low_bits.len().checked_add(high_bits.len()) else {
            memory::storage(&self.encoding);
            return Vec::new();
        };
        let Some(mut result) = self.counted_bits(width) else {
            return Vec::new();
        };
        result.extend(low_bits);
        result.extend(high_bits);
        result
    }
}
