// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

// Store/select axioms: https://smt-lib.org/theories-ArraysEx.shtml
// BV add/sub are modulo 2^64, with unsigned guards:
// https://smt-lib.org/theories-FixedSizeBitVectors.shtml
use super::{map_intern, BigInt, Builder, Result, Sort, TermData, TermId};

impl Builder<'_, '_> {
    pub(super) fn range(
        &mut self,
        destination: TermId,
        source: TermId,
        lo: &BigInt,
        hi: &BigInt,
        source_lo: &BigInt,
        sort: &Sort,
    ) -> Result<TermId> {
        let admission = &mut self.admission;
        let bound = self
            .terms
            .try_fresh_bv64_binder_with_progress(&mut |work, bytes| {
                admission.pay(work, bytes).is_ok()
            })
            .map_err(map_intern)?;
        let low = self.bound(lo)?;
        let high = self.bound(hi)?;
        let offset = self.bound(source_lo)?;
        let bv64 = Sort::bitvec(64);
        let lower = self.app("bvule", &[low, bound], &Sort::Bool)?;
        let upper = self.app("bvult", &[bound, high], &Sort::Bool)?;
        let condition = self.app("and", &[lower, upper], &Sort::Bool)?;
        let shifted = self.app("bvsub", &[bound, low], &bv64)?;
        let mapped = self.app("bvadd", &[shifted, offset], &bv64)?;
        let element = super::validate::element(sort)?;
        let copied = self.app("select", &[source, mapped], element)?;
        let preserved = self.app("select", &[destination, bound], element)?;
        self.admission.pay(64, 0)?;
        let body = self.intern(&TermData::Ite(condition, copied, preserved), element)?;
        self.app("lambda-array", &[bound, body], sort)
    }
}
