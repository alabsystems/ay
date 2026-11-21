// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-owned accounting for diagnostic native INPUT export.

/// Resource dimension exhausted by an input capture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum NativeReplayExportResource {
    /// Source visits, raw bytes inspected, and serialization work.
    Work,
    /// Conservative cumulative owned allocation charges.
    Storage,
    /// Bytes written to complete JSON outputs, including failed attempts.
    Output,
    /// Recursive source or serialization nesting.
    Depth,
}

/// Explicit diagnostic capture allowances. These do not configure solving.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeReplayExportLimits {
    pub(crate) max_work: usize,
    pub(crate) max_storage_bytes: usize,
    pub(crate) max_output_bytes: usize,
    pub(crate) max_depth: usize,
}

impl NativeReplayExportLimits {
    /// Construct independent work, owned-storage, output, and nesting limits.
    /// Zero is a real zero allowance; no limit is silently enlarged.
    #[must_use]
    pub const fn new(
        max_work: usize,
        max_storage_bytes: usize,
        max_output_bytes: usize,
        max_depth: usize,
    ) -> Self {
        Self {
            max_work,
            max_storage_bytes,
            max_output_bytes,
            max_depth,
        }
    }
}

/// Cumulative usage of one caller-owned export budget.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NativeReplayExportUsage {
    /// Work charged before source traversal, comparison, copying or writing.
    pub work: usize,
    /// Conservative owned capacity/allocation charges, never internally reset.
    pub storage_bytes: usize,
    /// JSON bytes written, including bytes discarded after refusal.
    pub output_bytes: usize,
}

/// Explicit diagnostic refusal. It contains no copied user-controlled payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum NativeReplayExportError {
    /// A caller allowance was exhausted or its arithmetic overflowed.
    #[error(
        "native INPUT export exceeded {resource:?} allowance {limit} (requested total {requested})"
    )]
    Limit {
        /// Exhausted resource.
        resource: NativeReplayExportResource,
        /// Applicable caller allowance or the v1 reader's nesting envelope.
        limit: usize,
        /// Attempted cumulative usage, saturated on arithmetic overflow.
        requested: usize,
    },
    /// Caller cancellation, including a callback panic caught by its owner.
    #[error("native INPUT export cancelled")]
    Cancelled,
    /// The producer graph cannot be represented faithfully by native v1.
    #[error("native INPUT export refused source shape {shape}")]
    UnsupportedSource {
        /// Static shape classification; never a raw source/debug rendering.
        shape: &'static str,
    },
    /// A term reference is outside the producer arena.
    #[error("native INPUT export encountered invalid term ID {term}")]
    InvalidTerm {
        /// Invalid numeric handle.
        term: u32,
    },
    /// A bounded buffer reservation failed.
    #[error("native INPUT export could not reserve bounded storage")]
    Allocation,
    /// JSON serialization failed after bounded source admission.
    #[error("native INPUT export JSON encoding failed")]
    Encoding,
}

/// Reusable cumulative budget for diagnostic capture only.
///
/// Export never resets this object. The first refusal is sticky, so a stopped
/// attempt cannot retry its way around its owner's envelope. Storage counts
/// conservative allocation/capacity charges, rather than allocator bookkeeping
/// or process RSS. User callbacks and disposal of caller-owned inputs are outside
/// these counters. This value is not proof or replay admission authority.
#[derive(Debug)]
pub struct NativeReplayExportBudget {
    pub(crate) limits: NativeReplayExportLimits,
    pub(crate) usage: NativeReplayExportUsage,
    pub(crate) refusal: Option<NativeReplayExportError>,
}

impl NativeReplayExportBudget {
    /// Start a new caller-owned capture envelope.
    #[must_use]
    pub const fn new(limits: NativeReplayExportLimits) -> Self {
        Self {
            limits,
            usage: NativeReplayExportUsage {
                work: 0,
                storage_bytes: 0,
                output_bytes: 0,
            },
            refusal: None,
        }
    }

    /// Read cumulative usage without resetting it.
    #[must_use]
    pub const fn usage(&self) -> NativeReplayExportUsage {
        self.usage
    }

    /// Read the first refusal, when capture has stopped.
    #[must_use]
    pub const fn refusal(&self) -> Option<NativeReplayExportError> {
        self.refusal
    }
}
