// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-size observations of one controlled read, never proof or budget authority.

use super::{retained, ProofCheckError};

/// The actual original transaction boundary where the first rejection surfaced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadStage {
    /// Before any retained bytes are decoded.
    Entry,
    /// While the retained transport is decoded.
    Decode,
    /// While the decoded proof is replayed strictly.
    StrictReplay,
    /// During the caller's final control observation.
    FinalControl,
}

/// A first decoder error or strict-check class, without owned diagnostic text.
/// A transport limit reports its actual decoder numbers before public flattening.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadRefusal {
    /// A decoder resource count exceeded its transport ceiling.
    TransportLimit {
        /// The resource whose ceiling was exceeded.
        resource: &'static str,
        /// The observed resource count.
        actual: usize,
        /// The configured ceiling.
        limit: usize,
    },
    /// The caller's transport control refused further work.
    TransportRefused,
    /// The transport deadline expired.
    TransportDeadline,
    /// Transport size arithmetic overflowed.
    TransportOverflow,
    /// A transport allocation failed.
    TransportAllocation,
    /// The retained transport was malformed.
    TransportInvalid,
    /// Strict proof replay exhausted its resource owner.
    ProofResourceLimit,
    /// Strict proof replay was cancelled.
    ProofCancelled,
    /// Strict proof replay rejected the proof semantically.
    ProofRejected,
}

/// Observational data only: it cannot authorize a retry, report or ledger reset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RetainedReadFailure {
    /// The transaction stage where the first rejection surfaced.
    pub stage: RetainedReadStage,
    /// The fixed refusal class observed at that stage.
    pub refusal: RetainedReadRefusal,
}

/// The unchanged public error class; semantic rejection details stay in its error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadErrorClass {
    /// The caller's original resource envelope was exhausted.
    ResourceLimit,
    /// The caller's original cancellation control fired.
    Cancelled,
    /// Any semantic or structural rejection.
    OtherRejection,
}

/// The original outer control's existing terminal observation, not an extra poll.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RetainedReadTerminal {
    /// The final observation found the original control healthy.
    Healthy,
    /// The original control had already refused before final observation.
    AlreadyRefused(RetainedReadErrorClass),
    /// The final observation was the first refusal.
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
    /// Returns the first fixed-size refusal observation, if one was recorded.
    pub fn first_failure(&self) -> Option<RetainedReadFailure> {
        self.first
    }

    /// Returns the original control's final observation, if one was recorded.
    pub fn terminal(&self) -> Option<RetainedReadTerminal> {
        self.terminal
    }

    /// Returns the public error class ultimately reported to the caller.
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
