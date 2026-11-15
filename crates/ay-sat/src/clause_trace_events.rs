// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retirement events share the bounded literal arena without entering proof replay.

use super::{ClauseEventOrigin, ClauseTrace, ClauseTraceEntryRef, EntryMeta};
use crate::literal::Literal;
use std::mem::size_of;

impl ClauseTrace {
    pub(crate) fn set_event_capture(&mut self, policy: super::ClauseEventCapture) {
        self.event_capture = policy;
    }

    /// Whether every retirement since trace creation was retained on request.
    pub fn captures_full_lifecycle(&self) -> bool {
        self.event_capture == super::ClauseEventCapture::Lifecycle && !self.retirements_omitted
    }

    pub(super) fn deletion_bytes(&self) -> usize {
        self.deletions
            .capacity()
            .saturating_mul(size_of::<(usize, EntryMeta)>())
    }

    /// Actual solver retirement, before the stored literals disappear.
    pub(crate) fn record_deletion(&mut self, id: u64, clause: &[Literal]) {
        if self.event_capture == super::ClauseEventCapture::Additions {
            self.retirements_omitted = true;
            return;
        }
        self.solver_num_vars = None;
        if !self.original_event_open(false) {
            self.mark_proof_work_exhausted();
            return;
        }
        let accepted = self.try_record_deletion(id, clause);
        if !accepted {
            self.is_truncated = true;
        }
    }

    fn try_record_deletion(&mut self, id: u64, clause: &[Literal]) -> bool {
        let Some(mut meta) = self.preflight_entry_meta(id, clause, false, &[]) else {
            return false;
        };
        // Reuse the ordinary arena's checked current+replacement capacity plan.
        if !self.reserve_for_add(clause.len(), 0) {
            return false;
        }
        if self.deletions.len() == self.deletions.capacity() {
            let Some(required) = self.deletions.len().checked_add(1) else {
                return false;
            };
            let available = self.budget_bytes.saturating_sub(self.used_bytes())
                / size_of::<(usize, EntryMeta)>();
            if required > available {
                return false;
            }
            let capacity = required.saturating_mul(2).min(available);
            let Some(bytes) = capacity.checked_mul(size_of::<(usize, EntryMeta)>()) else {
                return false;
            };
            if self
                .used_bytes()
                .checked_add(bytes)
                .is_none_or(|n| n > self.budget_bytes)
            {
                return false;
            }
            let mut replacement = Vec::new();
            if replacement.try_reserve_exact(capacity).is_err() {
                return false;
            }
            let actual = replacement
                .capacity()
                .saturating_mul(size_of::<(usize, EntryMeta)>());
            if self
                .used_bytes()
                .checked_add(actual)
                .is_none_or(|n| n > self.budget_bytes)
            {
                return false;
            }
            replacement.extend_from_slice(&self.deletions);
            self.deletions = replacement;
        }
        meta.origin = ClauseEventOrigin::Deleted;
        let Some(position) = usize::try_from(self.originals.count)
            .ok()
            .and_then(|count| self.meta.len().checked_add(count))
        else {
            return false;
        };
        self.lit_pool.extend_from_slice(clause);
        self.deletions.push((position, meta));
        true
    }

    /// Insertions and actual retirements in original solver order. Ordinary
    /// `entries()` deliberately remains addition-only for proof reconstruction.
    pub fn events(&self) -> impl Iterator<Item = ClauseTraceEntryRef<'_>> {
        let entries = self.entries();
        let mut additions = entries.iter();
        let mut deleted = self.deletions.iter().peekable();
        let mut position = 0usize;
        std::iter::from_fn(move || {
            if deleted.peek().is_some_and(|(after, _)| *after == position) {
                let (_, meta) = deleted.next()?;
                return Some(entries.view(meta));
            }
            let addition = additions.next()?;
            position += 1;
            Some(addition)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Variable;

    #[test]
    fn ordinary_proof_retirement_uses_no_event_storage_or_late_capture_authority() {
        let mut trace = ClauseTrace::new();
        let a = Literal::positive(Variable::new(0));
        trace.add_clause_with_hint_slices(1, &[a], true, &[]);
        let bytes = trace.used_bytes();
        trace.record_deletion(1, &[a]);
        assert_eq!(trace.used_bytes(), bytes);
        assert_eq!(trace.len(), 1);
        assert!(!trace.is_truncated());
        trace.set_event_capture(super::super::ClauseEventCapture::Lifecycle);
        assert!(!trace.captures_full_lifecycle());
    }

    #[test]
    fn retirement_order_does_not_change_proof_additions_or_old_snapshots() {
        let mut trace = ClauseTrace::new();
        trace.set_event_capture(super::super::ClauseEventCapture::Lifecycle);
        let a = Literal::positive(Variable::new(0));
        trace.add_clause_with_hint_slices(1, &[a], true, &[]);
        let before = trace.clone();
        trace.record_deletion(1, &[a]);
        trace.add_clause_with_hint_slices(2, &[a.negated()], false, &[1]);
        let events: Vec<_> = trace.events().collect();
        assert_eq!(events.len(), 3);
        assert_eq!(events[0].id, 1);
        assert_eq!(events[1].origin, ClauseEventOrigin::Deleted);
        assert_eq!(events[1].clause, &[a]);
        assert_eq!(events[2].id, 2);
        assert_eq!(trace.len(), 2);
        assert_eq!(
            trace.entries().last().expect("addition").resolution_hints,
            &[1]
        );
        assert_eq!(before.events().count(), 1);
        assert!(trace.used_bytes() <= trace.budget_bytes);
    }

    #[test]
    fn exhausted_retirement_storage_refuses_complete_event_publication() {
        let mut trace = ClauseTrace::new();
        trace.set_event_capture(super::super::ClauseEventCapture::Lifecycle);
        let a = Literal::positive(Variable::new(0));
        trace.add_clause_with_hint_slices(1, &[a], true, &[]);
        trace.budget_bytes = trace.used_bytes();
        trace.record_deletion(1, &[a]);
        assert!(trace.is_truncated());
        assert_eq!(trace.events().count(), 1);
        assert_eq!(trace.len(), 1);
    }
}
