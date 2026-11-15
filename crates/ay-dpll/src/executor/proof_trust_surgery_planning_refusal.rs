// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unbounded-population. The name the canonical work estimator gives its own
//! refusal.
//!
//! A private child of `proof_trust_surgery_planning_budget` so the estimator
//! and the vocabulary it reports in stay together without either file growing
//! past its ceiling.

/// Why `canonical_term_work` refused a root, when it refused one.
///
/// #unbounded-population. The override plan (`authored-surface-override-plan-
/// unbounded`) declines on this estimator's bare `None`, and a `None` for a
/// binder below the root is a SHAPE veto the estimator applies at any size,
/// while a `None` on visits, depth or bytes is a SIZE refusal. A census that
/// cannot tell them apart ranks a schema gap as a budget gap.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalWorkRefusal {
    /// A `let`, `forall` or `exists` below the root.
    Binder,
    /// More than `MAX_VISITS` per-occurrence visits.
    Visits,
    /// Deeper than `MAX_DEPTH`.
    Depth,
    /// More than `MAX_BYTES` of rendered payload.
    Bytes,
    /// An unpriceable symbol or constant.
    Symbol,
}

impl CanonicalWorkRefusal {
    /// The fixed name this refusal carries on the disclosure line.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Binder => "binder",
            Self::Visits => "visits",
            Self::Depth => "depth",
            Self::Bytes => "bytes",
            Self::Symbol => "symbol",
        }
    }
}
