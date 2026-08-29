// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! The frontend-neutral verdict.
//!
//! AY's verified result [`ay_chc::VerifiedChcResult`] is `Safe` / `Unsafe` /
//! `Unknown`, where each variant is construction-sealed and carries AY-internal
//! evidence ([`ay_chc::VerifiedInvariant`], [`ay_chc::VerifiedCounterexample`],
//! [`ay_chc::VerifiedUnknownMarker`]). Both frontends then re-map that into
//! their own status types (model-checker-consumer → `VerificationStatus`, ty →
//! `Bmc/PdrResult`).
//!
//! [`AyVerdict`] is the single intermediate they both map *from*, so the
//! `VerifiedChcResult` → neutral-verdict translation is written once here:
//!
//! - `Safe`    → [`AyVerdict::Proved`] (`Option<Certificate>`: present iff a
//!   proof run was requested and produced one),
//! - `Unsafe`  → [`AyVerdict::Violated`] (carrying a [`Model`] view of the cex),
//! - `Unknown` → [`AyVerdict::Unknown`] (carrying a normalized [`UnknownReason`]
//!   plus the original AY free-text reason rendering as `detail`).

use ay_chc::{Counterexample, InvariantModel, VerifiedChcResult, VerifiedUnknownReason};

use crate::proof::Certificate;

/// Frontend-neutral verdict over an AY run.
#[derive(Debug)]
#[non_exhaustive]
#[must_use = "a verdict encodes a correctness outcome and must be consumed"]
pub enum AyVerdict {
    /// The property holds (AY `Safe`).
    ///
    /// `invariant` is the synthesized inductive [`Invariant`] AY validated for
    /// this `Safe` result; it is always present (every `VerifiedChcResult::Safe`
    /// carries a [`InvariantModel`]) so frontends that surface the invariant
    /// (e.g. the model-checker consumer's `PdrResult::Safe { invariant }`) read it directly.
    ///
    /// `certificate` is the re-checkable proof artifact bundle: present when a
    /// proof run was requested and AY produced evidence; `None` on the fast
    /// portfolio path. Boxed because that bundle is large relative to the
    /// `Violated`/`Unknown` payloads.
    Proved {
        /// The validated inductive invariant for the `Safe` result.
        invariant: Invariant,
        /// The re-checkable proof certificate, if a proof run produced one.
        certificate: Option<Box<Certificate>>,
    },
    /// The property is violated (AY `Unsafe`), with a counterexample model.
    Violated(Model),
    /// AY could not decide within budget, with a normalized reason.
    ///
    /// `reason` is the 1:1 normalization of AY's sealed reason enum (the stable
    /// machine-routing bucket). `detail` preserves AY's original free-text
    /// `Display` rendering of the underlying [`ay_chc::VerifiedUnknownMarker`]
    /// (e.g. "unknown (BMC searched to max_depth=8 without finding a
    /// counterexample; not a safety proof)") so frontends can surface the exact
    /// diagnostic AY produced (G4). It is `None` only for a future/unrecognized
    /// `VerifiedChcResult` variant that carries no marker.
    Unknown {
        /// The normalized machine-routing reason bucket.
        reason: UnknownReason,
        /// AY's original free-text reason rendering, when available.
        detail: Option<String>,
    },
}

/// A view of an AY `Unsafe` counterexample.
///
/// Wraps AY's verified [`Counterexample`] without re-modeling it; frontends
/// read steps out for trace reconstruction (model-checker-consumer `FailedProperties`,
/// ty `BmcResult::Violation { trace }`).
#[derive(Debug, Clone)]
pub struct Model {
    /// The verified counterexample trace from AY.
    pub counterexample: Counterexample,
}

impl Model {
    /// Number of steps in the counterexample trace.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.counterexample.steps.len()
    }
}

/// A view of an AY `Safe` invariant model.
///
/// Surfaced for callers that want the synthesized inductive invariant (e.g.
/// the model-checker consumer's `PdrResult::Safe { invariant }`). The proof-grade artifact, when
/// requested, lives in [`Certificate`] instead.
#[derive(Debug, Clone)]
pub struct Invariant {
    /// The verified invariant model from AY.
    pub model: InvariantModel,
}

/// Why AY returned `Unknown`.
///
/// A 1:1 normalization of [`ay_chc::VerifiedUnknownReason`] so frontends do not
/// each re-match the sealed AY enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnknownReason {
    /// Solver ran but could not conclude.
    Inconclusive,
    /// BMC exhausted its bounded search space (no cex up to the bound).
    BmcExhaustedSearch,
    /// BMC ran out of its budget before exhausting the search.
    BmcBudgetExhausted,
    /// The engine was not applicable to this problem shape.
    NotApplicable,
}

impl From<VerifiedUnknownReason> for UnknownReason {
    fn from(r: VerifiedUnknownReason) -> Self {
        match r {
            VerifiedUnknownReason::Inconclusive => Self::Inconclusive,
            VerifiedUnknownReason::BmcExhaustedSearch => Self::BmcExhaustedSearch,
            VerifiedUnknownReason::BmcBudgetExhausted => Self::BmcBudgetExhausted,
            VerifiedUnknownReason::NotApplicable => Self::NotApplicable,
            // `VerifiedUnknownReason` is `#[non_exhaustive]`; map unseen
            // future reasons to the safest neutral bucket.
            _ => Self::Inconclusive,
        }
    }
}

/// Normalize an [`ay_chc::VerifiedChcResult`] into an [`AyVerdict`].
///
/// On `Safe`, the validated inductive invariant is lifted out of the sealed
/// [`ay_chc::VerifiedInvariant`] into the neutral [`Invariant`] view and placed
/// on the [`AyVerdict::Proved`] arm. `certificate` is threaded alongside it:
/// pass `None` on the fast portfolio path and `Some(..)` when a proof run
/// produced re-checkable evidence.
pub fn from_verified(
    result: VerifiedChcResult,
    certificate: Option<Box<Certificate>>,
) -> AyVerdict {
    match result {
        VerifiedChcResult::Safe(inv) => AyVerdict::Proved {
            invariant: Invariant {
                model: inv.into_inner(),
            },
            certificate,
        },
        VerifiedChcResult::Unsafe(cex) => AyVerdict::Violated(Model {
            counterexample: cex.counterexample().clone(),
        }),
        VerifiedChcResult::Unknown(marker) => AyVerdict::Unknown {
            // `VerifiedUnknownMarker`'s `Display` renders AY's full diagnostic
            // (reason + BMC depth context). Capture it before lifting the
            // normalized reason bucket so model-checker-consumer/ty keep the exact text AY
            // emitted (G4).
            detail: Some(marker.to_string()),
            reason: marker.reason().into(),
        },
        // `VerifiedChcResult` is `#[non_exhaustive]`; an unrecognized future
        // variant carries no marker, so there is no AY free-text to preserve.
        _ => AyVerdict::Unknown {
            reason: UnknownReason::Inconclusive,
            detail: None,
        },
    }
}
