// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepaid bounds for the unchanged heap, VMTF and bucket selectors.

use super::*;
use crate::counted_storage::Result;
use crate::solver::lifecycle::VarState;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

#[cfg(test)]
mod tests;

impl VSIDS {
    pub(crate) fn admit_heap_selection(
        &self,
        vals: &[i8],
        states: &[VarState],
        domain: Option<&[bool]>,
        owner: &CountedAdmission,
    ) -> Result<usize> {
        owner.admit(4, 0)?; // root/children/tail metadata and phase selection
        let Some(&root) = self.heap.first() else {
            return Ok(0);
        };
        let available = |var: u32| {
            let i = var as usize;
            vals[i * 2] == 0 && !states.get(i).is_some_and(|state| state.is_removed())
        };
        let eligible = |var: u32| {
            available(var) && domain.is_none_or(|bits| bits.get(var as usize) == Some(&true))
        };
        if eligible(root) {
            return Ok(0);
        }
        // A root deletion replaces it with max(tail, its children). This O(1)
        // fast bound covers the normal one-assigned-root prune; it avoids a
        // whole-heap debit on every ordinary EVSIDS decision. Other cases use
        // the complete prune/reinsert bound, not a predicted search result.
        let mut next = self.heap.last().copied().filter(|_| self.heap.len() > 1);
        for index in [1, 2] {
            if let Some(&candidate) = self.heap.get(index) {
                if next.is_none_or(|best| self.var_less(candidate as usize, best as usize)) {
                    next = Some(candidate);
                }
            }
        }
        if next.is_none_or(eligible) {
            let depth = (usize::BITS - self.heap.len().leading_zeros()) as usize;
            owner.admit(2 * depth + 4, 0)?;
            return Ok(usize::from(domain.is_some() && available(root)));
        }
        let required = self.admit_domain_heap_selection(owner)?;
        Ok(if domain.is_some() { required } else { 0 })
    }

    pub(crate) fn admit_domain_heap_selection(&self, owner: &CountedAdmission) -> Result<usize> {
        let length = self.heap.len();
        let depth = (usize::BITS - length.leading_zeros()) as usize;
        // Per initial member: selector visit, pop/remove, scratch bookkeeping,
        // and reinsertion; at most three root-to-leaf/leaf-to-root traversals.
        let work = length
            .checked_mul(3 * depth + 5)
            .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
        owner.admit(work, 0)?;
        Ok(length)
    }

    pub(crate) fn admit_bucket_selection(&self, owner: &CountedAdmission) -> Result<()> {
        self.bucket_queue.admit_selection(owner)
    }

    pub(crate) fn admit_vmtf_selection(
        &self,
        vals: &[i8],
        states: &[VarState],
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        let start = if self.vmtf_unassigned == INVALID_VAR {
            self.vmtf_last
        } else {
            self.vmtf_unassigned
        };
        if self.admit_vmtf_walk(start, vals, states, owner)? || start == self.vmtf_last {
            return Ok(());
        }
        self.admit_vmtf_walk(self.vmtf_last, vals, states, owner)
            .map(|_| ())
    }

    fn admit_vmtf_walk(
        &self,
        mut index: u32,
        vals: &[i8],
        states: &[VarState],
        owner: &CountedAdmission,
    ) -> Result<bool> {
        while index != INVALID_VAR {
            // One read-only planning visit and the corresponding real visit.
            owner.admit(2, 0)?;
            let i = index as usize;
            if vals[i * 2] == 0 && !states.get(i).is_some_and(|state| state.is_removed()) {
                return Ok(true);
            }
            index = self.vmtf_prev[i];
        }
        Ok(false)
    }
}
