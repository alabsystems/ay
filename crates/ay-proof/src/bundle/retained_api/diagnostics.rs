// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-size observations of one controlled read, never proof or budget authority.

use super::{retained, ProofCheckError};

/// The actual original transaction boundary where the first rejection surfaced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadStage {
    Entry,
    Decode,
    StrictReplay,
    FinalControl,
}

/// A first decoder error or strict-check class, without owned diagnostic text.
/// A transport limit reports its actual decoder numbers before public flattening.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadRefusal {
    TransportLimit {
        resource: &'static str,
        actual: usize,
        limit: usize,
    },
    TransportRefused,
    TransportDeadline,
    TransportOverflow,
    TransportAllocation,
    TransportInvalid,
    ProofResourceLimit,
    ProofCancelled,
    ProofRejected,
}

/// Observational data only: it cannot authorize a retry, report or ledger reset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetainedReadFailure {
    pub stage: RetainedReadStage,
    pub refusal: RetainedReadRefusal,
}

/// The unchanged public error class; semantic rejection details stay in its error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadErrorClass {
    ResourceLimit,
    Cancelled,
    OtherRejection,
}

/// The original outer control's existing terminal observation, not an extra poll.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadTerminal {
    Healthy,
    AlreadyRefused(RetainedReadErrorClass),
    NewlyRefused(RetainedReadErrorClass),
}

/// Stack-only first/error/terminal observations of exactly one read invocation.
/// None is no observation, not a healthy or complete proof credential. The header
/// does not retain a caller, deadline, ledger, payload or reusable authority.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RetainedReadDiagnostics {
    pub(super) first: Option<RetainedReadFailure>,
    pub(super) terminal: Option<RetainedReadTerminal>,
    pub(super) reported: Option<RetainedReadErrorClass>,
}

impl RetainedReadDiagnostics {
    pub fn first_failure(&self) -> Option<RetainedReadFailure> {
        self.first
    }

    pub fn terminal(&self) -> Option<RetainedReadTerminal> {
        self.terminal
    }

    pub fn reported_error(&self) -> Option<RetainedReadErrorClass> {
        self.reported
    }
}

impl RetainedReadErrorClass {
    pub(super) fn of(error: &ProofCheckError) -> Self {
        match error {
            ProofCheckError::ResourceLimit => Self::ResourceLimit,
            ProofCheckError::Cancelled => Self::Cancelled,
            _ => Self::OtherRejection,
        }
    }
}

pub(super) fn transport(first: &mut Option<RetainedReadFailure>, error: retained::TransportError) {
    use retained::TransportError;
    let refusal = match error {
        TransportError::Limit {
            resource,
            actual,
            limit,
        } => RetainedReadRefusal::TransportLimit {
            resource,
            actual,
            limit,
        },
        TransportError::Refused => RetainedReadRefusal::TransportRefused,
        TransportError::Deadline => RetainedReadRefusal::TransportDeadline,
        TransportError::Overflow => RetainedReadRefusal::TransportOverflow,
        TransportError::Allocation => RetainedReadRefusal::TransportAllocation,
        _ => RetainedReadRefusal::TransportInvalid,
    };
    first.get_or_insert(RetainedReadFailure {
        stage: RetainedReadStage::Decode,
        refusal,
    });
}

pub(super) fn proof(
    first: &mut Option<RetainedReadFailure>,
    stage: RetainedReadStage,
    error: &ProofCheckError,
) {
    let refusal = match error {
        ProofCheckError::ResourceLimit => RetainedReadRefusal::ProofResourceLimit,
        ProofCheckError::Cancelled => RetainedReadRefusal::ProofCancelled,
        _ => RetainedReadRefusal::ProofRejected,
    };
    first.get_or_insert(RetainedReadFailure { stage, refusal });
}
