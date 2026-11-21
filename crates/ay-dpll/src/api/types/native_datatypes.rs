// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::SolverError;

/// Cumulative resource allowances for a native monomorphic declarations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeDatatypeBatchLimits {
    pub(crate) work: usize,
    pub(crate) storage: usize,
    pub(crate) depth: usize,
}

impl NativeDatatypeBatchLimits {
    /// Zero remains a zero allowance. Limits do not change solving policy.
    #[must_use]
    pub const fn new(work: usize, storage: usize, depth: usize) -> Self {
        Self {
            work,
            storage,
            depth,
        }
    }
}

/// Charges are conservative cumulative source/lookup work and owned capacity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NativeDatatypeBatchUsage {
    /// Charged before source visits, table probes and command construction.
    pub work: usize,
    /// Charged before owned copies, scratch contexts and registry growth.
    pub storage_bytes: usize,
}

/// A bounded declaration refusal, containing no user-controlled allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum NativeDatatypeBatchRefusal {
    /// Source/work allowance exhausted.
    #[error("native declaration work limit {limit} exceeded (requested {requested})")]
    Work {
        /// Limit.
        limit: usize,
        /// Requested cumulative work.
        requested: usize,
    },
    /// Owned capacity allowance exhausted.
    #[error("native declaration storage limit {limit} exceeded (requested {requested})")]
    Storage {
        /// Limit.
        limit: usize,
        /// Requested cumulative storage.
        requested: usize,
    },
    /// Recursive input exceeds the allowed depth.
    #[error("native declaration depth limit {limit} exceeded (requested {requested})")]
    Depth {
        /// Limit.
        limit: usize,
        /// Requested depth.
        requested: usize,
    },
    /// Caller stop, solver interrupt or resource stop was observed pre-commit.
    #[error("native declaration cancelled before commit")]
    Cancelled,
    /// A bounded reservation failed.
    #[error("native declaration allocation refused")]
    Allocation,
    /// Current source context cannot be admitted by the monomorphic route.
    #[error("native declaration unsupported source: {shape}")]
    UnsupportedSource {
        /// Static shape.
        shape: &'static str,
    },
}

/// Native group errors preserve the actual frontend declaration diagnostic.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum NativeDatatypeBatchError {
    /// Explicit admission/cancellation refusal; no group mutation occurred.
    #[error(transparent)]
    Refused(#[from] NativeDatatypeBatchRefusal),
    /// A user declaration error rejected atomically by the real frontend.
    #[error(transparent)]
    Declaration(#[from] SolverError),
}

/// Caller-owned sticky resource owner. Reusing it never resets its allowance.
/// It grants no declaration, term, model or proof authority.
#[derive(Debug)]
pub struct NativeDatatypeBatchBudget {
    pub(crate) limits: NativeDatatypeBatchLimits,
    pub(crate) usage: NativeDatatypeBatchUsage,
    pub(crate) refusal: Option<NativeDatatypeBatchRefusal>,
}

impl NativeDatatypeBatchBudget {
    /// Begin one resource envelope shared by all its declaration attempts.
    #[must_use]
    pub const fn new(limits: NativeDatatypeBatchLimits) -> Self {
        Self {
            limits,
            usage: NativeDatatypeBatchUsage {
                work: 0,
                storage_bytes: 0,
            },
            refusal: None,
        }
    }
    /// Return charged work/storage, including refused attempts.
    #[must_use]
    pub const fn usage(&self) -> NativeDatatypeBatchUsage {
        self.usage
    }
    /// Return the first sticky resource refusal, if any.
    #[must_use]
    pub const fn refusal(&self) -> Option<NativeDatatypeBatchRefusal> {
        self.refusal
    }
}
