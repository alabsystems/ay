// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation shared by the typed engine-economics builders.

use crate::tune::Knob;

/// A rejected [`super::EngineEconomics`] setting.
///
/// Returned at *construction*, not at solve time. The alternative — accept
/// anything and clamp during the solve — was measured to be the worse contract
/// for the crate's primary in-process consumer: `--sat-stop-mult=-1`
/// reached `Duration::mul_f64`, which panics, so a malformed value inherited
/// from a CI shell could abort a verifier worker mid-solve
/// (the development design notes §M1, consequence 3). A typed
/// error at the builder puts the failure where the caller can act on it, and
/// makes an accepted `EngineEconomics` a value the solve path can trust
/// without re-checking.
#[derive(Debug, Clone, Copy, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum EngineConfigError {
    /// A NaN or infinite setting.
    #[error("{knob} must be finite, got {value}")]
    NotFinite {
        /// The knob's stable name, as an operator would spell it.
        knob: &'static str,
        /// The rejected value.
        value: f64,
    },
    /// A finite setting outside the knob's admissible range.
    #[error("{knob} must lie in [{low}, {high}], got {value}")]
    OutOfRange {
        /// The knob's stable name, as an operator would spell it.
        knob: &'static str,
        /// The rejected value.
        value: f64,
        /// Inclusive lower bound.
        low: f64,
        /// Inclusive upper bound.
        high: f64,
    },
}

pub(super) fn checked(
    knob: Knob,
    value: f64,
    low: f64,
    high: f64,
) -> Result<f64, EngineConfigError> {
    if !value.is_finite() {
        return Err(EngineConfigError::NotFinite {
            knob: knob.label(),
            value,
        });
    }
    if value < low || value > high {
        return Err(EngineConfigError::OutOfRange {
            knob: knob.label(),
            value,
            low,
            high,
        });
    }
    Ok(value)
}

/// Seconds ceiling for a [`std::time::Duration`]-valued knob: the engine's own
/// real-knob domain, so the builder cannot admit a value the accessor would
/// then discard.
///
/// `Duration::MAX.as_secs_f64()` rounds *up* past `u64::MAX`, so a caller
/// spelling "no cap" as `Duration::MAX` would hand the consuming site a value
/// that panics `Duration::from_secs_f64` on the way back. Clamping — rather
/// than erroring — is right here because the intent is unambiguous: ~31 million
/// years is "no cap" by any reading, and refusing it would be pedantry, where a
/// negative share is a genuine mistake worth reporting.
pub(super) const MAX_KNOB_SECS: f64 = crate::tune::MAX_REAL;
