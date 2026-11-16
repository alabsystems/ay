// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Instant, Rc, ReplayLimit, ReplayMemory, RetainedProofTransportLimits, TermId};
use ay_dpll::api::{
    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF,
    MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
};
use std::mem::size_of;

use diagnostic::Refusal;

// The existing counted_limits_until codec ceiling (ay-proof producer_limits),
// separately downward-intersected with remaining aggregate request allowance.
const DOCUMENT_BYTES: usize = 192 * 1024 * 1024;
pub(crate) struct RetainedReplayProgress<'a> {
    limit: ReplayLimit<'a>,
    memory: ReplayMemory,
    deadline: Instant,
    request: Rc<()>,
    work: usize,
    bytes: usize,
    max_work: usize,
    max_bytes: usize,
    // Per-obligation work envelopes and the live-byte settlement slot.
    obligations: settlement::Obligations,
    stopped: bool,
    first_refusal: Option<Refusal>,
    callback: &'a mut dyn FnMut() -> bool,
}

mod diagnostic;
mod inventory;
mod settlement;
#[cfg(test)]
mod tests;
pub(crate) use settlement::Settlement;

impl<'a> RetainedReplayProgress<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        limit: ReplayLimit<'a>,
        callback: &'a mut dyn FnMut() -> bool,
    ) -> Result<Self, String> {
        Self::new_for_retained_rows(limit, callback, 1)
    }

    /// Owner for a request that may declare up to `rows` retained
    /// obligations. Bytes bound live memory under one proof's published
    /// ceiling and return when an obligation's proof owners drop. Work is
    /// one row's envelope per declared obligation and is never returned, so
    /// the cumulative work cap is at most `rows` envelopes.
    pub(crate) fn new_for_retained_rows(
        limit: ReplayLimit<'a>,
        callback: &'a mut dyn FnMut() -> bool,
        rows: usize,
    ) -> Result<Self, String> {
        limit
            .check_diagnostic()
            .map_err(|reason| Refusal::from(reason).message().to_string())?;
        let deadline = match limit {
            ReplayLimit::Until(deadline) | ReplayLimit::Cancellable { deadline, .. } => deadline,
        };
        let memory = ReplayMemory::capture(None);
        // Published whole-proof count times published per-lemma admission
        // bounds, times three for work: a retained row's metered walks (live
        // exact export capture and finish, the independent third replay, the
        // strict byte replay) are priced by reservation, and a single proof's
        // grant is exhausted by a legitimate BV-heavy row (a captured one
        // needs about 406M). That is ONE row's envelope, granted again per
        // declared obligation and never scaled by the row count; bytes bound
        // live memory and stay one proof's. Still finite request grants, not
        // a claim every maximal mixture fits.
        const RETAINED_WALKS_PER_ROW: usize = 3;
        let envelope = u64::try_from(MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF)
            .ok()
            .and_then(|count| count.checked_mul(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA))
            .and_then(|work| work.checked_mul(RETAINED_WALKS_PER_ROW as u64))
            .and_then(|work| usize::try_from(work).ok())
            .ok_or_else(|| "retained request work ceiling overflow".to_string())?;
        let max_bytes = MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF
            .checked_mul(MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA)
            .ok_or_else(|| "retained request byte ceiling overflow".to_string())?;
        let max_bytes = memory
            .term_limit()
            .map_or(max_bytes, |cap| cap.min(max_bytes));
        let mut owner = Self {
            limit,
            memory,
            deadline,
            request: Rc::new(()),
            work: 0,
            bytes: 0,
            max_work: envelope,
            max_bytes,
            obligations: settlement::Obligations::new(envelope, rows),
            stopped: false,
            first_refusal: None,
            callback,
        };
        #[cfg(test)]
        super::fee_census::owner(owner.max_work, owner.max_bytes);
        // The request identity and the settlement slot are two Rc<()>, two
        // reference counters each. Every bound row shares the identity and
        // never obtains a replacement ledger. These bytes are never settled.
        if !owner.charge(1, 4 * size_of::<usize>()) {
            return Err(owner.refusal_message().to_string());
        }
        Ok(owner)
    }

    #[cfg(test)]
    pub(crate) fn census_stage(&self, label: &'static str) -> super::fee_census::Stage {
        super::fee_census::stage(label)
    }

    pub(crate) fn deadline(&self) -> Instant {
        self.deadline
    }
    pub(crate) fn limit(&self) -> ReplayLimit<'a> {
        self.limit
    }
    pub(super) fn memory(&self) -> ReplayMemory {
        self.memory
    }

    /// Borrow only the already-recorded original owner's first refusal category.
    /// This does not poll, charge, format, clear the latch or authorize a report.
    pub(crate) fn diagnostic_refusal(&self) -> Option<&'static str> {
        self.first_refusal.map(Refusal::message)
    }

    pub(crate) fn check(&mut self) -> Result<(), String> {
        if self.charge(0, 0) {
            Ok(())
        } else {
            Err(self.refusal_message().to_string())
        }
    }

    pub(crate) fn charge(&mut self, work: usize, bytes: usize) -> bool {
        // A dropped settlement's bytes return before this admission decision.
        self.settle();
        if self.stopped {
            return false;
        }
        #[cfg(test)]
        super::fee_census::debit(
            work,
            bytes,
            self.work,
            self.bytes,
            self.max_work,
            self.max_bytes,
        );
        self.stopped = true;
        // Arithmetic/ceiling preflight precedes caller code: a debit that
        // cannot fit never invokes callbacks or starts additional work.
        let debit = bytes;
        let (work, bytes) = (self.work.checked_add(work), self.bytes.checked_add(bytes));
        let Some(work) = work else {
            return self.record_refusal(Refusal::WorkOverflow);
        };
        let Some(bytes) = bytes else {
            return self.record_refusal(Refusal::ByteOverflow);
        };
        if work > self.max_work {
            return self.record_refusal(Refusal::WorkCeiling);
        }
        if self.exceeds_envelope(work) {
            return self.record_refusal(Refusal::ObligationWorkCeiling);
        }
        if bytes > self.max_bytes {
            return self.record_refusal(Refusal::ByteCeiling);
        }
        if !self.controls_open() || !self.callback_open() {
            return false;
        }
        self.work = work;
        self.bytes = bytes;
        self.attribute(debit);
        if !self.controls_open() || !self.callback_open() {
            return false;
        }
        if !self.controls_open() {
            return false;
        }
        self.stopped = false;
        true
    }

    pub(crate) fn transport_limits(&mut self) -> RetainedProofTransportLimits {
        self.settle();
        let bytes = self.max_bytes.saturating_sub(self.bytes);
        let work = self.envelope_remaining(self.max_work.saturating_sub(self.work));
        RetainedProofTransportLimits {
            max_json_bytes: bytes.min(DOCUMENT_BYTES),
            max_storage_bytes: bytes.min(DOCUMENT_BYTES),
            max_work: u64::try_from(work)
                .unwrap_or(0)
                .min(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA),
        }
    }

    pub(super) fn refuse(&mut self, reason: &str) -> String {
        self.stopped = true;
        self.record_refusal(Refusal::ExplicitSourceOrProof);
        // Preserve the original operation's dynamic error text. The private
        // latch is a fixed-size category, not a second unpriced String copy.
        reason.to_string()
    }

    pub(super) fn request(&mut self) -> Result<Rc<()>, String> {
        if !self.charge(1, 0) {
            return Err(self.refuse("retained request identity refused"));
        }
        Ok(Rc::clone(&self.request))
    }

    pub(super) fn admits(&mut self, request: &Rc<()>) -> Result<(), String> {
        self.check()?;
        if Rc::ptr_eq(&self.request, request) {
            Ok(())
        } else {
            Err(self.refuse("retained capability belongs to a different request ledger"))
        }
    }
}
