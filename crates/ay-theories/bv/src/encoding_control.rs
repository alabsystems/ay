// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-local cooperative refusal, never SAT or proof authority.

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, OriginalAdmissionError};
use ay_core::resource::{current_check_stop, CheckStop};
use std::sync::atomic::AtomicU8;

pub(super) struct EncodingControl {
    counted: Option<CountedAdmission>,
    original: Option<CheckStop>,
    first_interrupt: OnceLock<Arc<AtomicBool>>,
    group: Option<ay_sys::MemoryGroupObservation>,
    enclosing: Option<(BvEncodingGuard, BvEncodingGuard)>,
    // One first refusal, including its known cause. None INSIDE the cell is
    // an opaque refusal, not permission to resume or invent a typed cause.
    refusal: OnceLock<Option<BlastCut>>,
    calling: AtomicBool,
    chunk: AtomicU8,
}

impl EncodingControl {
    pub(super) fn capture() -> Self {
        let captured = current_check_stop();
        let group = ay_sys::try_current_memory_group_observation();
        let refusal = OnceLock::new();
        if captured.is_err() || group.is_err() {
            let _ = refusal.set(None);
        }
        Self {
            counted: None,
            refusal,
            calling: AtomicBool::new(false),
            original: captured.ok().flatten(),
            first_interrupt: OnceLock::new(),
            group: group.ok().flatten(),
            enclosing: None,
            chunk: AtomicU8::new(0),
        }
    }

    fn joined(child: BvEncodingGuard, parent: BvEncodingGuard) -> Self {
        let refused = Self::inherited_refusal(&child, &parent);
        let joined = Self {
            counted: child.control.counted.clone(),
            original: None,
            first_interrupt: OnceLock::new(),
            group: None,
            enclosing: Some((child, parent)),
            refusal: OnceLock::new(),
            calling: AtomicBool::new(false),
            chunk: AtomicU8::new(0),
        };
        if let Some(cut) = refused {
            joined.refuse_with_cut(cut);
        }
        joined
    }

    pub(super) fn retain_first_interrupt(&self, flag: &Arc<AtomicBool>) {
        // Guards captured before the first attachment share this retained handle.
        let _ = self.first_interrupt.set(Arc::clone(flag));
    }

    pub(super) fn refuse(&self) {
        self.refuse_with_cut(None);
    }

    fn refuse_with_cut(&self, cut: Option<BlastCut>) {
        if self.refusal.set(cut).is_err() {
            return;
        }
        if let Some(owner) = &self.counted {
            let error = match cut {
                Some(BlastCut::MemoryCeiling) => CountedAdmissionError::Memory,
                _ => CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped),
            };
            owner.refuse(error);
        }
        if let Some((child, parent)) = &self.enclosing {
            child.control.refuse_with_cut(cut);
            parent.control.refuse_with_cut(cut);
        }
    }

    pub(super) fn was_stopped(&self) -> bool {
        self.refusal.get().is_some()
    }

    pub(super) fn blast_cut(&self) -> Option<BlastCut> {
        self.refusal.get().copied().flatten()
    }

    fn inherited_refusal(
        child: &BvEncodingGuard,
        parent: &BvEncodingGuard,
    ) -> Option<Option<BlastCut>> {
        if !child.open() {
            Some(child.control.blast_cut())
        } else if !parent.open() {
            Some(parent.control.blast_cut())
        } else {
            None
        }
    }

    fn open(&self, interrupt: Option<&Arc<AtomicBool>>) -> bool {
        // A reentrant callback cannot make a partially observed owner healthy.
        if self.was_stopped() {
            return false;
        }
        if self.calling.swap(true, Ordering::Relaxed) {
            self.refuse();
            return false;
        }
        let current = current_check_stop();
        let capture_failed = current.is_err();
        let current = current.ok().flatten();
        let different = current.as_ref().is_some_and(|current| {
            self.original
                .as_ref()
                .is_none_or(|original| !Arc::ptr_eq(current, original))
        });
        let inherited = self
            .enclosing
            .as_ref()
            .and_then(|(child, parent)| Self::inherited_refusal(child, parent));
        let refused = if self
            .counted
            .as_ref()
            .is_some_and(|owner| owner.check().is_err())
        {
            Some(None)
        } else if inherited.is_some() {
            inherited
        } else if capture_failed {
            Some(None)
        } else if self
            .first_interrupt
            .get()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            || interrupt.is_some_and(|flag| flag.load(Ordering::Relaxed))
        {
            Some(Some(BlastCut::Interrupt))
        } else if self.original.as_ref().is_some_and(|stop| stop())
            || (different && current.as_ref().is_some_and(|stop| stop()))
            || ay_core::resource::process_cancelled()
            || self.group.as_ref().is_some_and(|group| group.is_tripped())
        {
            Some(None)
        } else if ay_sys::process_memory_exceeded() {
            Some(Some(BlastCut::MemoryCeiling))
        } else if ay_sys::current_memory_group_soft_tripped() {
            Some(None)
        } else {
            None
        };
        if let Some(cut) = refused {
            self.refuse_with_cut(cut);
        }
        self.calling.store(false, Ordering::Relaxed);
        !self.was_stopped()
    }

    fn step(&self, interrupt: Option<&Arc<AtomicBool>>) -> bool {
        if self.was_stopped() {
            return false;
        }
        if self.counted.is_some() {
            return self.counted_admit(1, 0) && self.open(interrupt);
        }
        let next = self.chunk.fetch_add(1, Ordering::Relaxed).wrapping_add(1) & 63;
        next != 0 || self.open(interrupt)
    }
}

impl EncodingControl {
    pub(super) fn with_admission(owner: &CountedAdmission) -> Self {
        let mut control = Self::capture();
        control.counted = Some(owner.clone());
        control
    }

    pub(super) fn is_counted(&self) -> bool {
        self.counted.is_some()
    }

    pub(super) fn counted_refuse(&self, error: CountedAdmissionError) {
        if let Some(owner) = &self.counted {
            owner.refuse(error);
        }
        self.refuse();
    }

    pub(super) fn counted_admit(&self, work: usize, bytes: usize) -> bool {
        if self.was_stopped() {
            return false;
        }
        if let Some(owner) = &self.counted {
            if let Err(error) = owner.admit(work, bytes) {
                self.counted_refuse(error);
                return false;
            }
        }
        true
    }
}

/// Borrowed original encoding owner retained across temporary solver cleanup.
///
/// No new deadline, callback, work or memory allowance is created. Refusal is
/// shared with the encoding instance; `open` is cooperative, not atomic return.
#[derive(Clone)]
pub struct BvEncodingGuard {
    control: Arc<EncodingControl>,
    interrupt: Option<Arc<AtomicBool>>,
}

impl BvEncodingGuard {
    pub(super) fn same_owner(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.control, &other.control)
            && match (&self.interrupt, &other.interrupt) {
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                (None, None) => true,
                _ => false,
            }
    }

    pub(super) fn refuse_with_cut(&self, cut: Option<BlastCut>) {
        self.control.refuse_with_cut(cut);
    }

    /// Read only the monotone observed refusal; this does not poll or grant.
    #[must_use]
    pub fn was_stopped(&self) -> bool {
        self.control.was_stopped()
    }

    /// Decline publication after an observed original-owner refusal.
    #[must_use]
    pub fn open(&self) -> bool {
        self.control.open(self.interrupt.as_ref())
    }
}

impl BvSolver<'_> {
    /// Whether encoding remains admissible under its original stop owner.
    ///
    /// This is a cooperative resource fence, NOT a semantic proof. After any
    /// observed refusal, every result/export must be declined, including after
    /// raw flag replacement/reset or full encoding reset. Start a fresh solver
    /// for a genuinely fresh attempt; retaining a stopped original owner still
    /// refuses that fresh instance. Internal zero/empty unwind values are never
    /// circuits and must not be admitted as unconstrained success.
    #[must_use]
    pub fn encoding_complete(&self) -> bool {
        self.encoding.open(self.interrupt.as_ref())
    }

    /// Retain the same original refusal owner for a post-cleanup fence.
    #[must_use]
    pub fn encoding_guard(&self) -> BvEncodingGuard {
        BvEncodingGuard {
            control: Arc::clone(&self.encoding),
            interrupt: self.interrupt.clone(),
        }
    }

    /// Attach one enclosing root owner without creating recursive history.
    ///
    /// Exact self/same-parent attachment is idempotent, including raw-handle
    /// identity. A distinct second parent or a nested parent refuses both owners.
    /// Native temporary solvers attach once to a fresh query-local root. Neither
    /// native incremental caches nor CHC persistent caches retain these guards.
    pub fn inherit_encoding_guard(&mut self, guard: &BvEncodingGuard) {
        let child = self.encoding_guard();
        if child.same_owner(guard) {
            let _ = self.encoding_complete();
            return;
        }
        if let Some((_, parent)) = &self.encoding.enclosing {
            if parent.same_owner(guard) {
                let _ = self.encoding_complete();
                return;
            }
            self.encoding.refuse();
            guard.control.refuse();
            return;
        }
        if guard.control.enclosing.is_some() {
            self.encoding.refuse();
            guard.control.refuse();
            return;
        }
        self.encoding = Arc::new(EncodingControl::joined(child, guard.clone()));
        if !self.encoding_complete() {
            self.encoding.refuse();
        }
    }

    pub(super) fn encoding_step(&self) -> bool {
        self.encoding.step(self.interrupt.as_ref())
    }
}

#[cfg(test)]
mod tests;
