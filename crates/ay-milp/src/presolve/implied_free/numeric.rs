// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn equality_rhs(row: &WorkRow) -> Option<&BigRational> {
    row.lower
        .as_ref()
        .zip(row.upper.as_ref())
        .filter(|(lower, upper)| lower == upper)
        .map(|(value, _)| value)
}

pub(super) fn shift_bound(bound: &mut Option<BigRational>, shift: &BigRational) -> Option<()> {
    if let Some(value) = bound {
        *value -= shift;
        if !rational_fits(value) || exact_f64(value).is_none() {
            return None;
        }
    }
    Some(())
}

pub(super) fn zero_satisfies(lower: &Option<BigRational>, upper: &Option<BigRational>) -> bool {
    lower
        .as_ref()
        .is_none_or(|value| value <= &BigRational::zero())
        && upper
            .as_ref()
            .is_none_or(|value| value >= &BigRational::zero())
}

pub(super) fn rational_fits(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

pub(super) fn exact_f64(value: &BigRational) -> Option<f64> {
    let value_f64 = value.to_f64()?;
    (value_f64.is_finite() && BigRational::from_float(value_f64).as_ref() == Some(value))
        .then_some(value_f64)
}

pub(super) fn bound_f64(value: &Option<BigRational>, lower: bool) -> Option<f64> {
    match value {
        Some(value) => exact_f64(value),
        None if lower => Some(f64::NEG_INFINITY),
        None => Some(f64::INFINITY),
    }
}

pub(super) fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

/// Whether the pass is armed. DEFAULT OFF: this landed as a salvaged lane
/// with June-era measurements only, so the shipped trajectory stays
/// byte-identical and the arm waits for its corpus A/B like `StructElim`
/// did (see `struct_elim_enabled`).
///
/// DELIBERATELY NOT CACHED. It is an arm selector, and `tests/env_ledger.rs`
/// records why every arm selector must be a live read: a `OnceLock` latches
/// the first value a process sees, and a sweep whose second arm silently
/// re-runs the first records the wrong result as a finding.
pub(crate) fn enabled() -> bool {
    crate::tune::caller_flag(crate::tune::Knob::AffineAgg) == Some(true)
}

/// Cached trace predicate; see the live-read ratchet in `tests/env_ledger.rs`.
pub(super) fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// Cached diagnostic accessor; forced at the public solve boundary by
/// `bab::prime_env_all` so no worker first-touches `getenv` mid-solve.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
