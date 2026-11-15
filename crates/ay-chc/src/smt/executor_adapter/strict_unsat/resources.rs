// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One original deadline/token and cumulative accounted-proof allocation cap.

use super::{ReplayLimit, ReplayMemory};
use ay_core::TermId;

#[cfg(test)]
thread_local! {
    /// Test seam: runs after every ADMITTED charge, so a test can land a stop
    /// exactly after the last poll a completed check makes.
    pub(super) static AFTER_CHARGE: std::cell::RefCell<Option<Box<dyn FnMut()>>> =
        const { std::cell::RefCell::new(None) };
}

pub(super) struct ProofProgress<'a> {
    limit: ReplayLimit<'a>,
    memory: ReplayMemory,
    work: usize,
    bytes: usize,
    stopped: bool,
}

impl<'a> ProofProgress<'a> {
    pub(super) fn new(limit: ReplayLimit<'a>, memory: ReplayMemory) -> Self {
        Self {
            limit,
            memory,
            work: 0,
            bytes: 0,
            stopped: false,
        }
    }

    /// Export charges the resident solver term ledger once, then every
    /// accounted export/replay copy shares this counter. It is cumulative
    /// allocation accounting, not live RSS or an allocator-completeness claim.
    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        if self.stopped {
            return false;
        }
        self.stopped = true;
        if self.limit.check().is_none() || self.memory.check().is_none() {
            return false;
        }
        let (Some(work), Some(bytes)) =
            (self.work.checked_add(work), self.bytes.checked_add(bytes))
        else {
            return false;
        };
        if self.memory.term_limit().is_some_and(|cap| bytes > cap) {
            return false;
        }
        self.work = work;
        self.bytes = bytes;
        self.stopped = false;
        #[cfg(test)]
        AFTER_CHARGE.with(|hook| {
            if let Some(hook) = hook.borrow_mut().as_mut() {
                hook();
            }
        });
        true
    }

    pub(super) fn ordered_unique(&mut self, terms: &[TermId]) -> Option<Vec<TermId>> {
        let Some(bytes) = terms.len().checked_mul(std::mem::size_of::<TermId>()) else {
            self.stopped = true;
            return None;
        };
        if !self.charge(terms.len(), bytes) {
            return None;
        }
        let mut unique = Vec::new();
        if unique.try_reserve_exact(terms.len()).is_err() {
            self.stopped = true;
            return None;
        }
        for &term in terms {
            if !self.charge(1, 0) {
                return None;
            }
            let mut present = false;
            for &previous in &unique {
                if !self.charge(1, 0) {
                    return None;
                }
                if previous == term {
                    present = true;
                    break;
                }
            }
            if !present {
                unique.push(term);
            }
        }
        self.charge(0, 0).then_some(unique)
    }

    pub(super) fn equal_ids(&mut self, left: &[TermId], right: &[TermId]) -> bool {
        if !self.charge(1, 0) || left.len() != right.len() {
            return false;
        }
        // #completed-check-accepted: the limit is polled before each
        // comparison, never after the last one; an equal binding is final.
        for (a, b) in left.iter().zip(right) {
            if !self.charge(1, 0) || a != b {
                return false;
            }
        }
        true
    }
}

#[cfg(test)]
mod tests;
