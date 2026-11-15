// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{OriginalAdmissionError, QueryError};
use crate::original_query::StopReason;
use crate::resource::{CheckStopCaptureError, Exhausted};

/// Version of the admission receipt, not of a solver's work-unit definition.
pub const COUNTED_ADMISSION_USAGE_VERSION: u32 = 1;

/// The first refusal of a counted invocation. No variant is a solver verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum CountedAdmissionError {
    /// The next positive work debit exceeds the invocation's remaining grant.
    #[error("the original work grant is exhausted")]
    WorkExhausted,
    /// The next logical allocation/copy debit exceeds the cumulative grant.
    #[error("the original cumulative logical-storage grant is exhausted")]
    StorageExhausted,
    /// A retained or enclosing GuardTree authority stopped the invocation.
    #[error("an original or enclosing resource guard refused: {0:?}")]
    Guard(Exhausted),
    /// A retained memory group or process memory ceiling stopped the invocation.
    #[error("the original or current memory observation refused")]
    Memory,
    /// The ambient callback could not be safely observed; absence is unproven.
    #[error("the original callback could not be captured: {0}")]
    CallbackCapture(CheckStopCaptureError),
    /// The ambient memory authority could not be safely captured.
    #[error("the original memory observation could not be captured")]
    MemoryCapture,
    /// A compatibility adapter or opaque callback supplied the terminal cause.
    #[error(transparent)]
    Original(#[from] OriginalAdmissionError),
}

impl CountedAdmissionError {
    pub(super) fn legacy(self) -> OriginalAdmissionError {
        match self {
            Self::Original(error) => error,
            Self::Guard(Exhausted::Cancelled) => {
                OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Cancelled))
            }
            Self::Guard(Exhausted::Deadline | Exhausted::Cpu) => {
                OriginalAdmissionError::Query(QueryError::Interrupted(StopReason::Deadline))
            }
            _ => OriginalAdmissionError::Query(QueryError::Exhausted),
        }
    }
}

/// A bounded snapshot of the SAME ledger used by every clone and adapter.
///
/// Counts are successfully admitted work and cumulative logical copy/storage,
/// not elapsed time, live RSS, SAT conflicts, or a guarantee that every solver
/// operation was instrumented. Failed paired admissions debit neither balance.
/// Zero-cost polls do not consume work. The snapshot is diagnostic only: it
/// neither polls external controls nor authorizes a result or later operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct AdmissionUsage {
    /// Receipt schema, independent of the solver's work-unit definition.
    pub version: u32,
    /// Original work credit transferred at construction, never replenished.
    pub work_granted: u64,
    /// Sum of successfully admitted work debits, not necessarily completed work.
    pub work_admitted: u64,
    /// Work credit not yet admitted; it grants nothing after a refusal.
    pub work_remaining: u64,
    /// Original cumulative logical-storage credit, not a live-RSS ceiling.
    pub storage_granted: usize,
    /// Sum of successfully admitted logical allocation/copy debits.
    pub storage_admitted: usize,
    /// Logical-storage credit not yet admitted; cleanup does not refund it.
    pub storage_remaining: usize,
    /// The first terminal cause shared by every retained clone and adapter.
    pub refusal: Option<CountedAdmissionError>,
}
