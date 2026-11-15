// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Per-obligation work envelopes and RAII settlement of transient proof bytes.
//!
//! The byte ceiling bounds LIVE logical memory. Bytes debited while a
//! [`Settlement`] is live belong to the proof or checker owners that hold it.
//! Only dropping that token, together with them, returns those bytes, and the
//! ledger applies the return before its next admission decision; a leaked
//! token never refunds. Work is never returned: each declared obligation gets
//! one row's work envelope of its own, the cumulative work cap grows by one
//! envelope per obligation after the first, and a request declares at most
//! its retained row count of obligations. A request that declares no
//! obligation keeps its cumulative one-row ledger; its settlements are inert.

use super::{diagnostic::Refusal, Rc, RetainedReplayProgress};

/// Obligation and settlement state of one request ledger.
pub(super) struct Obligations {
    /// One row's work: each obligation's own ceiling, and the cumulative
    /// grant every obligation after the first adds.
    pub(super) envelope: usize,
    /// At most this many obligations may be declared.
    rows: usize,
    declared: usize,
    /// Cumulative work when the current obligation began.
    floor: usize,
    /// Cloned into the live settlement. Its strong count is the only
    /// liveness signal: no timer or estimate returns bytes.
    slot: Rc<()>,
    /// Bytes debited while the current settlement is live.
    open: Option<usize>,
}

impl Obligations {
    pub(super) fn new(envelope: usize, rows: usize) -> Self {
        Self {
            envelope,
            rows,
            declared: 0,
            floor: 0,
            slot: Rc::new(()),
            open: None,
        }
    }
}

/// Held by the owner of one obligation's transient proof or checker state.
/// Its drop is the only event that returns that state's debited bytes.
/// While it is live, every byte the request debits is attributed to it, so a
/// caller must not admit request-lifetime allocations under a live token.
pub(crate) struct Settlement {
    slot: Option<Rc<()>>,
}

impl Settlement {
    /// Whether dropping this token returns bytes to the request ledger.
    pub(crate) fn settles(&self) -> bool {
        self.slot.is_some()
    }
}

impl RetainedReplayProgress<'_> {
    /// Open the next retained obligation: one row's work envelope of its own,
    /// and one more envelope of cumulative work after the first. Every earlier
    /// settlement must already be dropped. No work, debit or control poll.
    pub(crate) fn begin_obligation(&mut self) -> Result<(), String> {
        self.settle();
        if self.stopped {
            return Err(self.refusal_message().to_string());
        }
        if self.obligations.open.is_some() {
            return Err(self.refuse("retained obligation began while a proof owner is live"));
        }
        let declared = self.obligations.declared;
        let max_work = match declared {
            0 => Some(self.max_work),
            _ => self.max_work.checked_add(self.obligations.envelope),
        };
        let refusal = match max_work {
            _ if declared >= self.obligations.rows => Refusal::ObligationCount,
            None => Refusal::WorkOverflow,
            Some(max_work) => {
                self.max_work = max_work;
                self.obligations.declared = declared + 1;
                self.obligations.floor = self.work;
                return Ok(());
            }
        };
        self.stopped = true;
        self.record_refusal(refusal);
        Err(self.refusal_message().to_string())
    }

    /// The settlement for this obligation's transient proof or checker
    /// owners. Inert before any obligation is declared; never nested.
    pub(crate) fn settlement(&mut self) -> Result<Settlement, String> {
        self.settle();
        if self.obligations.declared == 0 {
            return Ok(Settlement { slot: None });
        }
        if self.obligations.open.is_some() {
            return Err(self.refuse("retained proof settlement cannot nest"));
        }
        self.obligations.open = Some(0);
        Ok(Settlement {
            slot: Some(Rc::clone(&self.obligations.slot)),
        })
    }

    /// Whether proposed cumulative `work` leaves the open obligation's envelope.
    pub(super) fn exceeds_envelope(&self, work: usize) -> bool {
        self.obligations.declared != 0
            && work
                .checked_sub(self.obligations.floor)
                .is_none_or(|used| used > self.obligations.envelope)
    }

    /// `cumulative` remaining work, narrowed to the open obligation's envelope.
    pub(super) fn envelope_remaining(&self, cumulative: usize) -> usize {
        if self.obligations.declared == 0 {
            return cumulative;
        }
        let used = self.work.saturating_sub(self.obligations.floor);
        cumulative.min(self.obligations.envelope.saturating_sub(used))
    }

    pub(super) fn attribute(&mut self, bytes: usize) {
        if let Some(open) = &mut self.obligations.open {
            // Never saturates: the account is part of the checked total.
            *open = open.saturating_add(bytes);
        }
    }

    /// Return the bytes of a dropped settlement. A live token keeps them.
    pub(super) fn settle(&mut self) {
        let Some(refund) = self.obligations.open else {
            return;
        };
        if Rc::strong_count(&self.obligations.slot) > 1 {
            return;
        }
        self.obligations.open = None;
        match self.bytes.checked_sub(refund) {
            Some(bytes) => self.bytes = bytes,
            None => {
                self.stopped = true;
                self.record_refusal(Refusal::SettlementUnderflow);
            }
        }
    }

    /// Cumulative work and live bytes, with their current ceilings.
    #[cfg(test)]
    pub(crate) fn ledger(&self) -> (usize, usize, usize, usize) {
        (self.work, self.bytes, self.max_work, self.max_bytes)
    }
}
