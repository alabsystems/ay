// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::RetainedReplayProgress;
use crate::smt::executor_adapter::replay_limit::ReplayLimitRefusal;

/// First original-owner refusal category, never proof/source authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Refusal {
    WorkOverflow,
    ByteOverflow,
    WorkCeiling,
    ObligationWorkCeiling,
    ObligationCount,
    ByteCeiling,
    SettlementUnderflow,
    OriginalDeadline,
    InheritedCancellation,
    ZeroTermMemory,
    TermOrProcessMemory,
    CallbackDidNotReturn,
    CallbackReturnedFalse,
    ExplicitSourceOrProof,
}

impl Refusal {
    pub(super) fn message(self) -> &'static str {
        match self {
            Self::WorkOverflow => "retained request cumulative work debit overflow",
            Self::ByteOverflow => "retained request cumulative byte debit overflow",
            Self::WorkCeiling => "retained request cumulative work ceiling exceeded",
            Self::ObligationWorkCeiling => "retained obligation work envelope exceeded",
            Self::ObligationCount => "retained request declared more obligations than retained rows",
            Self::ByteCeiling => "retained request live byte ceiling exceeded",
            Self::SettlementUnderflow => "retained request settlement exceeds its recorded byte debits",
            Self::OriginalDeadline => "retained request original wall deadline expired",
            Self::InheritedCancellation => "retained request inherited cancellation observed",
            Self::ZeroTermMemory => "retained request captured zero term-memory allowance",
            Self::TermOrProcessMemory => "retained request original term/process memory observer refused",
            Self::CallbackDidNotReturn => "retained request original callback did not return; owner remains stopped",
            Self::CallbackReturnedFalse => "retained request original callback returned false",
            Self::ExplicitSourceOrProof => "retained request prior explicit source/proof refusal; original operation retains its cause",
        }
    }
}

impl From<ReplayLimitRefusal> for Refusal {
    fn from(reason: ReplayLimitRefusal) -> Self {
        match reason {
            ReplayLimitRefusal::OriginalDeadline => Self::OriginalDeadline,
            ReplayLimitRefusal::InheritedCancellation => Self::InheritedCancellation,
        }
    }
}

impl RetainedReplayProgress<'_> {
    pub(super) fn refusal_message(&self) -> &'static str {
        self.first_refusal.map_or(
            "retained request stopped before a specific refusal was observed",
            Refusal::message,
        )
    }

    pub(super) fn record_refusal(&mut self, reason: Refusal) -> bool {
        if self.first_refusal.is_none() {
            self.first_refusal = Some(reason);
        }
        false
    }

    pub(super) fn controls_open(&mut self) -> bool {
        if let Err(reason) = self
            .limit
            .check_diagnostic_with_owner_deadline(self.deadline)
        {
            return self.record_refusal(reason.into());
        }
        if self.memory.check().is_none() {
            let reason = if self.memory.term_limit() == Some(0) {
                Refusal::ZeroTermMemory
            } else {
                Refusal::TermOrProcessMemory
            };
            return self.record_refusal(reason);
        }
        true
    }

    pub(super) fn callback_open(&mut self) -> bool {
        // The existing stopped latch is already set before entry. This marker
        // describes only non-return, not a fabricated panic or resource cause.
        self.first_refusal = Some(Refusal::CallbackDidNotReturn);
        if !(self.callback)() {
            self.first_refusal = Some(Refusal::CallbackReturnedFalse);
            return false;
        }
        self.first_refusal = None;
        true
    }
}
