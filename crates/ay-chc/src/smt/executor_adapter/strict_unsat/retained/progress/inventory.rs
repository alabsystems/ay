// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{size_of, RetainedReplayProgress, TermId};

impl RetainedReplayProgress<'_> {
    pub(crate) fn ordered_unique(&mut self, terms: &[TermId]) -> Result<Vec<TermId>, String> {
        let bytes = terms
            .len()
            .checked_mul(size_of::<TermId>())
            .ok_or_else(|| self.refuse("retained assumption inventory size overflow"))?;
        if !self.charge(terms.len(), bytes) {
            return Err(self.refuse("retained assumption inventory resource refusal"));
        }
        let mut unique = Vec::new();
        unique
            .try_reserve_exact(terms.len())
            .map_err(|_| self.refuse("retained assumption inventory allocation refusal"))?;
        let actual = unique
            .capacity()
            .checked_mul(size_of::<TermId>())
            .ok_or_else(|| self.refuse("retained assumption capacity overflow"))?;
        if !self.charge(0, actual.saturating_sub(bytes)) {
            return Err(self.refuse("retained assumption capacity resource refusal"));
        }
        for &term in terms {
            if !self.charge(1, 0) {
                return Err(self.refuse("retained assumption work refusal"));
            }
            let mut present = false;
            for &prior in &unique {
                if !self.charge(1, 0) {
                    return Err(self.refuse("retained assumption comparison refusal"));
                }
                if prior == term {
                    present = true;
                    break;
                }
            }
            if !present {
                unique.push(term);
            }
        }
        self.check()?;
        Ok(unique)
    }

    pub(crate) fn equal_ids(&mut self, left: &[TermId], right: &[TermId]) -> bool {
        if !self.charge(1, 0) || left.len() != right.len() {
            return false;
        }
        for (left, right) in left.iter().zip(right) {
            if !self.charge(1, 0) || left != right {
                return false;
            }
        }
        self.charge(0, 0)
    }

    pub(in super::super) fn copied_query(&mut self, source: &str) -> Result<Vec<u8>, String> {
        if !self.charge(source.len(), source.len()) {
            return Err(self.refuse("retained original query copy refusal"));
        }
        let mut query = Vec::new();
        query
            .try_reserve_exact(source.len())
            .map_err(|_| self.refuse("retained original query allocation refusal"))?;
        if !self.charge(0, query.capacity().saturating_sub(source.len())) {
            return Err(self.refuse("retained original query capacity refusal"));
        }
        query.extend_from_slice(source.as_bytes());
        self.check()?;
        Ok(query)
    }
}
