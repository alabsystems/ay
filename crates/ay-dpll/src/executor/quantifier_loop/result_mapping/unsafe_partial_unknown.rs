// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed classification for unsafe partial quantifier candidates.

use super::{Executor, UnknownOrigin, UnknownReason};

impl Executor {
    /// Preserve the generic incomplete contract after a supported candidate
    /// interpretation was attempted; unsupported families remain explicitly
    /// classified as unhandled quantifiers.
    /// # Why the structural flag exists
    ///
    /// Both branches below describe the SAME situation — the MBQI-unsafe
    /// binder-sort guard fired, so a `Sat`/`Unknown` from the ground lane may
    /// not be published — and they differ only in whether a UF-completion
    /// candidate happened to be attempted first. The reason LABELS they record
    /// differ, though, and the self-contained SAT certificates are consulted by
    /// label (`quantifier_sat_cert_consult_admitted`): the `false` branch's
    /// `QuantifierUnhandled` is admitted, the `true` branch's generic
    /// `Incomplete` is not. Attempting a candidate therefore removed the
    /// certificates' chance to decide a query they can decide, which is a
    /// capability loss with no soundness justification — the certificates
    /// re-verify every assertion under an explicitly constructed interpretation
    /// and are grant-only.
    ///
    /// `unsafe_partial_quantifier_unknown` records the structural fact, so the
    /// consult gate reads the situation instead of the label. The reason strings
    /// and the published `:reason-unknown` are untouched.
    pub(super) fn record_unsafe_partial_unknown(&mut self, candidate_attempted: bool) {
        self.unsafe_partial_quantifier_unknown = true;
        if candidate_attempted {
            self.record_unknown_from_origin(UnknownOrigin::IncompleteSolverLane);
            self.record_unknown_diagnostic(
                UnknownReason::Incomplete,
                "a candidate interpretation could not discharge an unsafe partial quantifier; failing closed to Unknown",
            );
        } else {
            self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
        }
    }
}
